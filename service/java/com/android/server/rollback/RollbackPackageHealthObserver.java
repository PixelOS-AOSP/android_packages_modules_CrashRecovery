/*
 * Copyright (C) 2019 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.android.server.rollback;

import static com.android.server.PackageWatchdog.MITIGATION_RESULT_SUCCESS;
import static com.android.server.PackageWatchdog.failureReasonToLog;

import android.annotation.AnyThread;
import android.annotation.FlaggedApi;
import android.annotation.NonNull;
import android.annotation.Nullable;
import android.annotation.SuppressLint;
import android.annotation.SystemApi;
import android.annotation.WorkerThread;
import android.app.PendingIntent;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.pm.ApplicationInfo;
import android.content.pm.PackageInfo;
import android.content.pm.PackageManager;
import android.content.pm.VersionedPackage;
import android.content.rollback.PackageRollbackInfo;
import android.content.rollback.RollbackInfo;
import android.content.rollback.RollbackManager;
import android.os.Environment;
import android.os.Handler;
import android.os.HandlerThread;
import android.os.PowerManager;
import android.os.SystemClock;
import android.os.SystemProperties;
import android.provider.DeviceConfig;
import android.sysprop.CrashRecoveryProperties;
import android.util.ArraySet;
import android.util.FileUtils;
import android.util.Log;
import android.util.Slog;
import android.util.SparseArray;

import com.android.internal.annotations.VisibleForTesting;
import com.android.internal.util.Preconditions;
import com.android.modules.utils.HandlerExecutor;
import com.android.server.PackageWatchdog;
import com.android.server.PackageWatchdog.FailureReasons;
import com.android.server.PackageWatchdog.PackageHealthObserver;
import com.android.server.PackageWatchdog.PackageHealthObserverImpact;
import com.android.server.crashrecovery.CrashRecoveryUtils;
import com.android.server.crashrecovery.proto.CrashRecoveryStatsLog;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.time.Instant;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.concurrent.Executor;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;

/**
 * {@link PackageHealthObserver} for {@link RollbackManagerService}.
 * This class monitors crashes and triggers RollbackManager rollback accordingly.
 * It also monitors native crashes for some short while after boot.
 *
 * @hide
 */
@FlaggedApi(android.crashrecovery.flags.Flags.FLAG_ENABLE_CRASHRECOVERY)
@SuppressLint({"CallbackName"})
@SystemApi(client = SystemApi.Client.SYSTEM_SERVER)
public final class RollbackPackageHealthObserver implements PackageHealthObserver {
    private static final String TAG = "RollbackPackageHealthObserver";
    private static final String NAME = "rollback-observer";
    private static final String CLASS_NAME = RollbackPackageHealthObserver.class.getName();

    private static final int PERSISTENT_MASK = ApplicationInfo.FLAG_PERSISTENT
            | ApplicationInfo.FLAG_SYSTEM;

    private static final String PROP_DISABLE_HIGH_IMPACT_ROLLBACK_FLAG =
            "persist.device_config.configuration.disable_high_impact_rollback";

    private static final String PROP_OBSERVER_ROLLBACK_AVAILABILITY_MILLIS =
            "observer_rollback_availability_in_millis";

    // Rollbacks available for RollbackPackageHealthObserver for the first 14 days.
    private static final long DEFAULT_ROLLBACK_AVAILABILITY_DURATION_MILLIS =
            TimeUnit.DAYS.toMillis(14);

    private long mRollbackAvailabilityDurationInMillis =
            DEFAULT_ROLLBACK_AVAILABILITY_DURATION_MILLIS;

    private final Context mContext;
    private final Handler mHandler;
    private final Executor mExecutor;
    private final File mLastStagedRollbackIdsFile;
    private final File mTwoPhaseRollbackEnabledFile;
    private final File mRollbackTimestampsFile;
    private final Object mRollbackTimestampsFileLock = new Object();
    // Staged rollback ids that have been committed but their session is not yet ready
    private final Set<Integer> mPendingStagedRollbackIds = new ArraySet<>();
    // True if needing to roll back only rebootless apexes when native crash happens
    private boolean mTwoPhaseRollbackEnabled;

    // The timestamp when device is booted.
    // This is used as a reference for the timestamp recorded in mRollbackTimestampsFile.
    private long  mBootTimestamp;

    @VisibleForTesting
    public RollbackPackageHealthObserver(@NonNull Context context) {
        mContext = context;
        HandlerThread handlerThread = new HandlerThread("RollbackPackageHealthObserver");
        handlerThread.start();
        mHandler = new Handler(handlerThread.getLooper());
        mExecutor = new HandlerExecutor(getHandler());
        File dataDir = new File(Environment.getDataDirectory(), "rollback-observer");
        dataDir.mkdirs();
        mLastStagedRollbackIdsFile = new File(dataDir, "last-staged-rollback-ids");
        mTwoPhaseRollbackEnabledFile = new File(dataDir, "two-phase-rollback-enabled");
        mRollbackTimestampsFile = new File(dataDir, "rollback-timestamps");
        PackageWatchdog.getInstance(mContext).registerHealthObserver(context.getMainExecutor(),
                this);

        if (SystemProperties.getBoolean("sys.boot_completed", false)) {
            // Load the value from the file if system server has crashed and restarted
            mTwoPhaseRollbackEnabled = readBoolean(mTwoPhaseRollbackEnabledFile);
        } else {
            // Disable two-phase rollback for a normal reboot. We assume the rebootless apex
            // installed before reboot is stable if native crash didn't happen.
            mTwoPhaseRollbackEnabled = false;
            writeBoolean(mTwoPhaseRollbackEnabledFile, false);
        }

        if (com.android.crashrecovery.flags.Flags
                .configurePackageHealthObserverRollbackTimeout()) {
            getHandler().post(this::updateBootTimestamp);
            registerTimeChangeReceiver();
        }
    }

    private String getFailedPackageName(@Nullable VersionedPackage failedPackage,
            @FailureReasons int failureReason) {
        if (failureReason == PackageWatchdog.FAILURE_REASON_NATIVE_CRASH) {
            return SystemProperties.get(
                    "sys.init.updatable_crashing_process_name", "UNKNOWN_NATIVE");
        }
        if (failureReason == PackageWatchdog.FAILURE_REASON_BOOT_LOOP) {
            return "UNKNOWN_BOOT_LOOP";
        }
        return (failedPackage == null ? "UNKNOWN" : failedPackage.getPackageName());
    }

    @Override
    public int onHealthCheckFailed(@Nullable VersionedPackage failedPackage,
            @FailureReasons int failureReason, int mitigationCount) {
        int impact = PackageHealthObserverImpact.USER_IMPACT_LEVEL_0;
        List<RollbackInfo> availableRollbacks = getAvailableRollbacks();
        List<RollbackInfo> lowImpactRollbacks = getRollbacksAvailableForImpactLevel(
                availableRollbacks, PackageManager.ROLLBACK_USER_IMPACT_LOW);
        if (!lowImpactRollbacks.isEmpty()) {
            if (failureReason == PackageWatchdog.FAILURE_REASON_NATIVE_CRASH) {
                // For native crashes, we will directly roll back any available rollbacks at low
                // impact level
                impact = PackageHealthObserverImpact.USER_IMPACT_LEVEL_30;
            } else if (getRollbackForPackage(failedPackage, lowImpactRollbacks) != null) {
                // Rollback is available for crashing low impact package
                impact = PackageHealthObserverImpact.USER_IMPACT_LEVEL_30;
            } else {
                impact = PackageHealthObserverImpact.USER_IMPACT_LEVEL_70;
            }
        }

        Slog.i(TAG, "Checking available remediations for health check failure."
                + " failedPackage: " + getFailedPackageName(failedPackage, failureReason)
                + " failureReason: " + failureReasonToLog(failureReason)
                + " available impact: " + impact);
        return impact;
    }

    @Override
    public int onExecuteHealthCheckMitigation(@Nullable VersionedPackage failedPackage,
            @FailureReasons int rollbackReason, int mitigationCount) {
        String failedPackageName = getFailedPackageName(failedPackage, rollbackReason);
        Slog.i(TAG, "Executing remediation."
                + " failedPackage: " + failedPackageName
                + " rollbackReason: " + failureReasonToLog(rollbackReason)
                + " mitigationCount: " + mitigationCount);
        List<RollbackInfo> availableRollbacks = getAvailableRollbacks();
        if (rollbackReason == PackageWatchdog.FAILURE_REASON_NATIVE_CRASH) {
            mHandler.post(() -> rollbackAllLowImpact(availableRollbacks, failedPackageName,
                    rollbackReason));
            return MITIGATION_RESULT_SUCCESS;
        }

        List<RollbackInfo> lowImpactRollbacks = getRollbacksAvailableForImpactLevel(
                availableRollbacks, PackageManager.ROLLBACK_USER_IMPACT_LOW);
        RollbackInfo rollback = getRollbackForPackage(failedPackage, lowImpactRollbacks);
        if (rollback != null) {
            mHandler.post(() -> rollbackPackage(rollback, failedPackage, rollbackReason,
                    failedPackageName));
        } else if (!lowImpactRollbacks.isEmpty()) {
            // Apply all available low impact rollbacks.
            mHandler.post(() -> rollbackAllLowImpact(availableRollbacks, failedPackageName,
                    rollbackReason));
        }

        // Assume rollbacks executed successfully
        return MITIGATION_RESULT_SUCCESS;
    }

    @Override
    public int onBootLoop(int mitigationCount) {
        int impact = PackageHealthObserverImpact.USER_IMPACT_LEVEL_0;
        List<RollbackInfo> availableRollbacks = getAvailableRollbacks();
        if (!availableRollbacks.isEmpty()) {
            impact = getUserImpactBasedOnRollbackImpactLevel(availableRollbacks);
        }
        return impact;
    }

    @Override
    public int onExecuteBootLoopMitigation(int mitigationCount) {
        List<RollbackInfo> availableRollbacks = getAvailableRollbacks();

        triggerLeastImpactLevelRollback(availableRollbacks,
                PackageWatchdog.FAILURE_REASON_BOOT_LOOP);
        return MITIGATION_RESULT_SUCCESS;
    }

    @Override
    @NonNull
    public String getUniqueIdentifier() {
        return NAME;
    }

    @Override
    public boolean isPersistent() {
        return true;
    }

    @Override
    public boolean mayObservePackage(@NonNull String packageName) {
        if (getAvailableRollbacks().isEmpty()) {
            return false;
        }
        return isPersistentSystemApp(packageName);
    }

    @VisibleForTesting
    List<RollbackInfo> getAvailableRollbacks() {
        final List<RollbackInfo> availableRollbacks =
                mContext.getSystemService(RollbackManager.class).getAvailableRollbacks();
        if (com.android.crashrecovery.flags.Flags
                .configurePackageHealthObserverRollbackTimeout()) {
            final SparseArray<String> rollbackTimestamps;
            synchronized (mRollbackTimestampsFileLock) {
                rollbackTimestamps = CrashRecoveryUtils.readAllKeyValues(mRollbackTimestampsFile);
            }
            return availableRollbacks.stream().filter(r -> {
                String timestamp = rollbackTimestamps.get(r.getRollbackId());
                // If the timestamp cannot be found, it means that such rollback is created before
                // installing the CrashRecovery version with "rollback-observer/rollback-timestamp".
                // On the safe side, it should be considered as available rollback.
                return timestamp == null || Instant.now().isBefore(Instant.parse(timestamp)
                        .plusMillis(mRollbackAvailabilityDurationInMillis));
            }).toList();
        }
        return availableRollbacks;
    }

    private boolean isPersistentSystemApp(@NonNull String packageName) {
        PackageManager pm = mContext.getPackageManager();
        try {
            ApplicationInfo info = pm.getApplicationInfo(packageName, 0);
            return (info.flags & PERSISTENT_MASK) == PERSISTENT_MASK;
        } catch (PackageManager.NameNotFoundException e) {
            return false;
        }
    }

    private void assertInWorkerThread() {
        Preconditions.checkState(mHandler.getLooper().isCurrentThread());
    }

    @AnyThread
    @NonNull
    public void notifyRollbackAvailable(@NonNull RollbackInfo rollback) {
        mHandler.post(() -> {
            if (com.android.crashrecovery.flags.Flags
                    .configurePackageHealthObserverRollbackTimeout()) {
                recordRollbackTimestamp(rollback, Instant.now());
            }
            // Enable two-phase rollback when a rebootless apex rollback is made available.
            // We assume the rebootless apex is stable and is less likely to be the cause
            // if native crash doesn't happen before reboot. So we will clear the flag and disable
            // two-phase rollback after reboot.
            if (isRebootlessApex(rollback)) {
                mTwoPhaseRollbackEnabled = true;
                writeBoolean(mTwoPhaseRollbackEnabledFile, true);
            }
        });
    }

    @VisibleForTesting
    void recordRollbackTimestamp(RollbackInfo rollback, Instant timestamp) {
        synchronized (mRollbackTimestampsFileLock) {
            CrashRecoveryUtils.putKeyValue(mRollbackTimestampsFile, rollback.getRollbackId(),
                    timestamp.toString());
        }
    }

    private static boolean isRebootlessApex(RollbackInfo rollback) {
        if (!rollback.isStaged()) {
            for (PackageRollbackInfo info : rollback.getPackages()) {
                if (info.isApex()) {
                    return true;
                }
            }
        }
        return false;
    }

    @WorkerThread
    private void updateRollbackAvailabilityDurationInMillis() {
        assertInWorkerThread();
        mRollbackAvailabilityDurationInMillis = DeviceConfig.getLong(
                DeviceConfig.NAMESPACE_ROLLBACK,
                PROP_OBSERVER_ROLLBACK_AVAILABILITY_MILLIS,
                DEFAULT_ROLLBACK_AVAILABILITY_DURATION_MILLIS);
        if (mRollbackAvailabilityDurationInMillis < 0) {
            mRollbackAvailabilityDurationInMillis = DEFAULT_ROLLBACK_AVAILABILITY_DURATION_MILLIS;
        }
        Slog.d(TAG, "mRollbackAvailabilityDurationInMillis=" +
                mRollbackAvailabilityDurationInMillis);
    }

    /** Verifies the rollback state after a reboot and schedules polling for sometime after reboot
     * to check for native crashes and mitigate them if needed.
     */
    @AnyThread
    public void onBootCompletedAsync() {
        mHandler.post(()->onBootCompleted());
    }

    @WorkerThread
    private void onBootCompleted() {
        assertInWorkerThread();

        if (com.android.crashrecovery.flags.Flags
                .configurePackageHealthObserverRollbackTimeout()) {
            DeviceConfig.addOnPropertiesChangedListener(DeviceConfig.NAMESPACE_ROLLBACK,
                    mExecutor, properties -> updateRollbackAvailabilityDurationInMillis());
            updateRollbackAvailabilityDurationInMillis();
        }
        RollbackManager rollbackManager = mContext.getSystemService(RollbackManager.class);
        if (!getAvailableRollbacks().isEmpty()) {
            // TODO(gavincorkery): Call into Package Watchdog from outside the observer
            PackageWatchdog.getInstance(mContext).scheduleCheckAndMitigateNativeCrashes();
        }

        SparseArray<String> rollbackIds = popLastStagedRollbackIds();
        for (int i = 0; i < rollbackIds.size(); i++) {
            WatchdogRollbackLogger.logRollbackStatusOnBoot(mContext,
                    rollbackIds.keyAt(i), rollbackIds.valueAt(i),
                    rollbackManager.getRecentlyCommittedRollbacks());
        }
    }

    @AnyThread
    private RollbackInfo getRollbackForPackage(@Nullable VersionedPackage failedPackage,
            List<RollbackInfo> availableRollbacks) {
        if (failedPackage == null) {
            return null;
        }

        for (RollbackInfo rollback : availableRollbacks) {
            for (PackageRollbackInfo packageRollback : rollback.getPackages()) {
                if (packageRollback.getVersionRolledBackFrom().equals(failedPackage)) {
                    return rollback;
                }
                // TODO(b/147666157): Extract version number of apk-in-apex so that we don't have
                //  to rely on complicated reasoning as below

                // Due to b/147666157, for apk in apex, we do not know the version we are rolling
                // back from. But if a package X is embedded in apex A exclusively (not embedded in
                // any other apex), which is not guaranteed, then it is sufficient to check only
                // package names here, as the version of failedPackage and the PackageRollbackInfo
                // can't be different. If failedPackage has a higher version, then it must have
                // been updated somehow. There are two ways: it was updated by an update of apex A
                // or updated directly as apk. In both cases, this rollback would have gotten
                // expired when onPackageReplaced() was called. Since the rollback exists, it has
                // same version as failedPackage.
                if (packageRollback.isApkInApex()
                        && packageRollback.getVersionRolledBackFrom().getPackageName()
                        .equals(failedPackage.getPackageName())) {
                    return rollback;
                }
            }
        }
        return null;
    }

    /**
     * Returns {@code true} if staged session associated with {@code rollbackId} was marked
     * as handled, {@code false} if already handled.
     */
    @WorkerThread
    private boolean markStagedSessionHandled(int rollbackId) {
        assertInWorkerThread();
        return mPendingStagedRollbackIds.remove(rollbackId);
    }

    /**
     * Returns {@code true} if all pending staged rollback sessions were marked as handled,
     * {@code false} if there is any left.
     */
    @WorkerThread
    private boolean isPendingStagedSessionsEmpty() {
        assertInWorkerThread();
        return mPendingStagedRollbackIds.isEmpty();
    }

    private static boolean readBoolean(File file) {
        try (FileInputStream fis = new FileInputStream(file)) {
            return fis.read() == 1;
        } catch (IOException ignore) {
            return false;
        }
    }

    private static void writeBoolean(File file, boolean value) {
        try (FileOutputStream fos = new FileOutputStream(file)) {
            fos.write(value ? 1 : 0);
            fos.flush();
            FileUtils.sync(fos);
        } catch (IOException ignore) {
        }
    }

    @WorkerThread
    private void saveStagedRollbackId(int stagedRollbackId, @Nullable VersionedPackage logPackage) {
        assertInWorkerThread();
        writeStagedRollbackId(mLastStagedRollbackIdsFile, stagedRollbackId, logPackage);
    }

    static void writeStagedRollbackId(File file, int stagedRollbackId,
            @Nullable VersionedPackage logPackage) {
        String logPackageName = logPackage != null ? logPackage.getPackageName() : "";
        CrashRecoveryUtils.putKeyValue(file, stagedRollbackId, logPackageName);
    }

    @WorkerThread
    private SparseArray<String> popLastStagedRollbackIds() {
        assertInWorkerThread();
        try {
            return readStagedRollbackIds(mLastStagedRollbackIdsFile);
        } finally {
            mLastStagedRollbackIdsFile.delete();
        }
    }

    static SparseArray<String> readStagedRollbackIds(File file) {
        return CrashRecoveryUtils.readAllKeyValues(file);
    }

    /**
     * Returns true if the package name is the name of a module.
     */
    @AnyThread
    private boolean isModule(String packageName) {
        // Check if the package is listed among the system modules or is an
        // APK inside an updatable APEX.
        try {
            PackageManager pm = mContext.getPackageManager();
            final PackageInfo pkg = pm.getPackageInfo(packageName, 0 /* flags */);
            String apexPackageName = pkg.getApexPackageName();
            if (apexPackageName != null) {
                packageName = apexPackageName;
            }

            return pm.getModuleInfo(packageName, 0 /* flags */) != null;
        } catch (PackageManager.NameNotFoundException e) {
            return false;
        }
    }

    /**
     * Rolls back the session that owns {@code failedPackage}
     *
     * @param rollback {@code rollbackInfo} of the {@code failedPackage}
     * @param failedPackage the package that needs to be rolled back
     */
    @WorkerThread
    private void rollbackPackage(RollbackInfo rollback, VersionedPackage failedPackage,
            @FailureReasons int rollbackReason, String failedPackageName) {
        assertInWorkerThread();

        Slog.i(TAG, "Rolling back package. RollbackId: " + rollback.getRollbackId()
                + " failedPackage: " + failedPackageName
                + " rollbackReason: " + failureReasonToLog(rollbackReason));
        CrashRecoveryUtils.logCrashRecoveryEvent(Log.DEBUG,
                String.format("Rolling back %s. Reason: %s", failedPackageName,
                        failureReasonToLog(rollbackReason)));
        final RollbackManager rollbackManager = mContext.getSystemService(RollbackManager.class);
        int reasonToLog = WatchdogRollbackLogger.mapFailureReasonToMetric(rollbackReason);

        VersionedPackage logPackageTemp = null;
        if (isModule(failedPackage.getPackageName())) {
            logPackageTemp = WatchdogRollbackLogger.getLogPackage(mContext, failedPackage);
        }

        final VersionedPackage logPackage = logPackageTemp;
        WatchdogRollbackLogger.logEvent(logPackage,
                CrashRecoveryStatsLog.WATCHDOG_ROLLBACK_OCCURRED__ROLLBACK_TYPE__ROLLBACK_INITIATE,
                reasonToLog, failedPackageName);

        Consumer<Intent> onResult = result -> {
            assertInWorkerThread();
            int status = result.getIntExtra(RollbackManager.EXTRA_STATUS,
                    RollbackManager.STATUS_FAILURE);
            if (status == RollbackManager.STATUS_SUCCESS) {
                if (rollback.isStaged()) {
                    int rollbackId = rollback.getRollbackId();
                    saveStagedRollbackId(rollbackId, logPackage);
                    WatchdogRollbackLogger.logEvent(logPackage,
                            CrashRecoveryStatsLog
                            .WATCHDOG_ROLLBACK_OCCURRED__ROLLBACK_TYPE__ROLLBACK_BOOT_TRIGGERED,
                            reasonToLog, failedPackageName);

                } else {
                    WatchdogRollbackLogger.logEvent(logPackage,
                            CrashRecoveryStatsLog
                                    .WATCHDOG_ROLLBACK_OCCURRED__ROLLBACK_TYPE__ROLLBACK_SUCCESS,
                            reasonToLog, failedPackageName);
                }
            } else {
                WatchdogRollbackLogger.logEvent(logPackage,
                        CrashRecoveryStatsLog
                                .WATCHDOG_ROLLBACK_OCCURRED__ROLLBACK_TYPE__ROLLBACK_FAILURE,
                        reasonToLog, failedPackageName);
            }
            if (rollback.isStaged()) {
                markStagedSessionHandled(rollback.getRollbackId());
                // Wait for all pending staged sessions to get handled before rebooting.
                if (isPendingStagedSessionsEmpty()) {
                    CrashRecoveryProperties.attemptingReboot(true);
                    mContext.getSystemService(PowerManager.class).reboot("Rollback staged install");
                }
            }
        };

        // Define a BroadcastReceiver to handle the result
        BroadcastReceiver rollbackReceiver = new BroadcastReceiver() {
            @Override
            public void onReceive(Context context, Intent result) {
                mHandler.post(() -> onResult.accept(result));
            }
        };

        String intentActionName = CLASS_NAME + rollback.getRollbackId();
        // Register the BroadcastReceiver
        mContext.registerReceiver(rollbackReceiver,
                new IntentFilter(intentActionName),
                Context.RECEIVER_NOT_EXPORTED);

        Intent intentReceiver = new Intent(intentActionName);
        intentReceiver.putExtra("rollbackId", rollback.getRollbackId());
        intentReceiver.setPackage(mContext.getPackageName());
        intentReceiver.setFlags(Intent.FLAG_RECEIVER_REGISTERED_ONLY);

        PendingIntent rollbackPendingIntent = PendingIntent.getBroadcast(mContext,
                rollback.getRollbackId(),
                intentReceiver,
                PendingIntent.FLAG_MUTABLE);

        rollbackManager.commitRollback(rollback.getRollbackId(),
                Collections.singletonList(failedPackage),
                rollbackPendingIntent.getIntentSender());
    }

    /**
     * Two-phase rollback:
     * 1. roll back rebootless apexes first
     * 2. roll back all remaining rollbacks if native crash doesn't stop after (1) is done
     *
     * This approach gives us a better chance to correctly attribute native crash to rebootless
     * apex update without rolling back Mainline updates which might contains critical security
     * fixes.
     */
    @WorkerThread
    private boolean useTwoPhaseRollback(List<RollbackInfo> rollbacks) {
        assertInWorkerThread();
        if (!mTwoPhaseRollbackEnabled) {
            return false;
        }

        Slog.i(TAG, "Rolling back all rebootless APEX rollbacks");
        boolean found = false;
        for (RollbackInfo rollback : rollbacks) {
            if (isRebootlessApex(rollback)) {
                VersionedPackage firstRollback =
                        rollback.getPackages().get(0).getVersionRolledBackFrom();
                rollbackPackage(rollback, firstRollback,
                        PackageWatchdog.FAILURE_REASON_NATIVE_CRASH,
                        getFailedPackageName(null, PackageWatchdog.FAILURE_REASON_NATIVE_CRASH));
                found = true;
            }
        }
        return found;
    }

    /**
     * Rollback the package that has minimum rollback impact level.
     * @param availableRollbacks all available rollbacks
     * @param rollbackReason reason to rollback
     */
    private void triggerLeastImpactLevelRollback(List<RollbackInfo> availableRollbacks,
            @FailureReasons int rollbackReason) {
        int minRollbackImpactLevel = getMinRollbackImpactLevel(availableRollbacks);

        if (minRollbackImpactLevel == PackageManager.ROLLBACK_USER_IMPACT_LOW) {
            // Apply all available low impact rollbacks.
            mHandler.post(() -> rollbackAllLowImpact(availableRollbacks,
                    getFailedPackageName(null, rollbackReason), rollbackReason));
        } else if (minRollbackImpactLevel == PackageManager.ROLLBACK_USER_IMPACT_HIGH) {
            // Check disable_high_impact_rollback device config before performing rollback
            if (SystemProperties.getBoolean(PROP_DISABLE_HIGH_IMPACT_ROLLBACK_FLAG, false)) {
                return;
            }
            // Rollback one package at a time. If that doesn't resolve the issue, rollback
            // next with same impact level.
            mHandler.post(() -> rollbackHighImpact(availableRollbacks, rollbackReason));
        }
    }

    /**
     * sort the available high impact rollbacks by first package name to have a deterministic order.
     * Apply the first available rollback.
     * @param availableRollbacks all available rollbacks
     * @param rollbackReason reason to rollback
     */
    @WorkerThread
    private void rollbackHighImpact(List<RollbackInfo> availableRollbacks,
            @FailureReasons int rollbackReason) {
        assertInWorkerThread();
        List<RollbackInfo> highImpactRollbacks =
                getRollbacksAvailableForImpactLevel(
                        availableRollbacks, PackageManager.ROLLBACK_USER_IMPACT_HIGH);

        // sort rollbacks based on package name of the first package. This is to have a
        // deterministic order of rollbacks.
        List<RollbackInfo> sortedHighImpactRollbacks = highImpactRollbacks.stream().sorted(
                Comparator.comparing(a -> a.getPackages().get(0).getPackageName())).toList();
        VersionedPackage firstRollback =
                sortedHighImpactRollbacks
                        .get(0)
                        .getPackages()
                        .get(0)
                        .getVersionRolledBackFrom();
        Slog.i(TAG, "Rolling back high impact rollback for package: "
                + firstRollback.getPackageName());
        rollbackPackage(sortedHighImpactRollbacks.get(0), firstRollback, rollbackReason,
                getFailedPackageName(null, rollbackReason));
    }

    /**
     * Rollback all available low impact rollbacks
     * @param availableRollbacks all available rollbacks
     * @param failedPackageName Name of package failed if any
     * @param rollbackReason reason to rollbacks
     */
    @WorkerThread
    private void rollbackAllLowImpact(
            List<RollbackInfo> availableRollbacks,
            String failedPackageName,
            @FailureReasons int rollbackReason) {
        assertInWorkerThread();

        List<RollbackInfo> lowImpactRollbacks = getRollbacksAvailableForImpactLevel(
                availableRollbacks,
                PackageManager.ROLLBACK_USER_IMPACT_LOW);
        if (useTwoPhaseRollback(lowImpactRollbacks)) {
            return;
        }

        Slog.i(TAG, "Rolling back all available low impact rollbacks due to " + failedPackageName);
        CrashRecoveryUtils.logCrashRecoveryEvent(Log.DEBUG,
                "Rolling back all available. Reason: " + failureReasonToLog(rollbackReason));
        // Add all rollback ids to mPendingStagedRollbackIds, so that we do not reboot before all
        // pending staged rollbacks are handled.
        for (RollbackInfo rollback : lowImpactRollbacks) {
            if (rollback.isStaged()) {
                mPendingStagedRollbackIds.add(rollback.getRollbackId());
            }
        }

        for (RollbackInfo rollback : lowImpactRollbacks) {
            VersionedPackage firstRollback =
                    rollback.getPackages().get(0).getVersionRolledBackFrom();
            rollbackPackage(rollback, firstRollback, rollbackReason, failedPackageName);
        }
    }

    private List<RollbackInfo> getRollbacksAvailableForImpactLevel(
            List<RollbackInfo> availableRollbacks, int impactLevel) {
        return availableRollbacks.stream()
                .filter(rollbackInfo -> rollbackInfo.getRollbackImpactLevel() == impactLevel)
                .toList();
    }

    private int getMinRollbackImpactLevel(List<RollbackInfo> availableRollbacks) {
        return availableRollbacks.stream()
                .mapToInt(RollbackInfo::getRollbackImpactLevel)
                .min()
                .orElse(-1);
    }

    private int getUserImpactBasedOnRollbackImpactLevel(List<RollbackInfo> availableRollbacks) {
        int impact = PackageHealthObserverImpact.USER_IMPACT_LEVEL_0;
        int minImpact = getMinRollbackImpactLevel(availableRollbacks);
        switch (minImpact) {
            case PackageManager.ROLLBACK_USER_IMPACT_LOW:
                impact = PackageHealthObserverImpact.USER_IMPACT_LEVEL_70;
                break;
            case PackageManager.ROLLBACK_USER_IMPACT_HIGH:
                if (!SystemProperties.getBoolean(PROP_DISABLE_HIGH_IMPACT_ROLLBACK_FLAG, false)) {
                    impact = PackageHealthObserverImpact.USER_IMPACT_LEVEL_90;
                }
                break;
            default:
                impact = PackageHealthObserverImpact.USER_IMPACT_LEVEL_0;
        }
        return impact;
    }

    @VisibleForTesting
    Handler getHandler() {
        return mHandler;
    }

    @AnyThread
    private void registerTimeChangeReceiver() {
        final BroadcastReceiver timeChangeIntentReceiver = new BroadcastReceiver() {
            @Override
            public void onReceive(Context context, Intent intent) {
                assertInWorkerThread();
                updateRollbackTimestampFile();
            }
        };
        final IntentFilter filter = new IntentFilter();
        filter.addAction(Intent.ACTION_TIME_CHANGED);
        mContext.registerReceiver(timeChangeIntentReceiver, filter,
                null /* broadcastPermission */, getHandler());
    }

    @VisibleForTesting
    void updateRollbackTimestampFile() {
        final long oldBootTimestamp = getBootTimestamp();
        final long offset = updateBootTimestamp() - oldBootTimestamp;

        synchronized (mRollbackTimestampsFileLock) {
            final SparseArray<String> rollbackTimestamps =
                    CrashRecoveryUtils.readAllKeyValues(mRollbackTimestampsFile);
            SparseArray<String> updatedRollbackTimestamps =
                    new SparseArray<>(rollbackTimestamps.size());
            for (int i = 0; i < rollbackTimestamps.size(); i++) {
                int rollbackId = rollbackTimestamps.keyAt(i);
                Instant updatedTimestamp =
                        Instant.parse(rollbackTimestamps.get(rollbackId)).plusMillis(
                                offset);
                updatedRollbackTimestamps.put(rollbackId, updatedTimestamp.toString());
            }
            CrashRecoveryUtils.writeAllKeyValues(mRollbackTimestampsFile,
                    updatedRollbackTimestamps);
        }
    }

    @VisibleForTesting
    @AnyThread
    long getBootTimestamp() {
        return mBootTimestamp;
    }

    @VisibleForTesting
    long updateBootTimestamp() {
        mBootTimestamp = System.currentTimeMillis() - SystemClock.elapsedRealtime();
        return mBootTimestamp;
    }
}
