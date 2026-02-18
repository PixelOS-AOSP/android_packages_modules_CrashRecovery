/*
 * Copyright (C) 2017 The Android Open Source Project
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

package com.android.server;

import static com.android.server.PackageWatchdog.MITIGATION_RESULT_SKIPPED;
import static com.android.server.PackageWatchdog.MITIGATION_RESULT_SUCCESS;
import static com.android.server.crashrecovery.CrashRecoveryUtils.logCrashRecoveryEvent;

import android.annotation.IntDef;
import android.annotation.NonNull;
import android.annotation.Nullable;
import android.content.Context;
import android.content.pm.ApplicationInfo;
import android.content.pm.PackageManager;
import android.content.pm.VersionedPackage;
import android.os.Build;
import android.os.Handler;
import android.os.HandlerThread;
import android.os.PowerManager;
import android.os.RecoverySystem;
import android.os.SystemClock;
import android.os.SystemProperties;
import android.provider.DeviceConfig;
import android.provider.Settings;
import android.sysprop.CrashRecoveryProperties;
import android.text.TextUtils;
import android.util.EventLog;
import android.util.FileUtils;
import android.util.Log;
import android.util.Slog;

import com.android.crashrecovery.flags.Flags;
import com.android.internal.annotations.GuardedBy;
import com.android.internal.annotations.VisibleForTesting;
import com.android.modules.utils.HandlerExecutor;
import com.android.server.PackageWatchdog.FailureReasons;
import com.android.server.PackageWatchdog.PackageHealthObserver;
import com.android.server.PackageWatchdog.PackageHealthObserverImpact;
import com.android.server.crashrecovery.CrashRecoveryUtils;
import com.android.server.crashrecovery.proto.CrashRecoveryStatsLog;

import java.io.File;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.concurrent.Executor;
import java.util.concurrent.TimeUnit;

/**
 * Utilities to help rescue the system from crash loops. Callers are expected to report boot events
 * and persistent app crashes, and if they happen frequently enough this class will slowly escalate
 * through several rescue operations before finally rebooting and prompting the user if they want to
 * wipe data as a last resort.
 *
 * @hide
 */
public class RescueParty {
    @VisibleForTesting static final String PROP_ENABLE_RESCUE = "persist.sys.enable_rescue";
    @VisibleForTesting static final int LEVEL_FACTORY_RESET = 5;
    @VisibleForTesting static final int RESCUE_LEVEL_NONE = 0;
    @VisibleForTesting static final int RESCUE_LEVEL_SCOPED_DEVICE_CONFIG_RESET = 1;
    @VisibleForTesting static final int RESCUE_LEVEL_ALL_DEVICE_CONFIG_RESET = 2;
    @VisibleForTesting static final int RESCUE_LEVEL_WARM_REBOOT = 3;
    @VisibleForTesting static final int RESCUE_LEVEL_RESET_SETTINGS_UNTRUSTED_DEFAULTS = 4;
    @VisibleForTesting static final int RESCUE_LEVEL_RESET_SETTINGS_UNTRUSTED_CHANGES = 5;
    @VisibleForTesting static final int RESCUE_LEVEL_RESET_SETTINGS_TRUSTED_DEFAULTS = 6;
    @VisibleForTesting static final int RESCUE_LEVEL_FACTORY_RESET = 7;

    @IntDef(
            prefix = {"RESCUE_LEVEL_"},
            value = {
                RESCUE_LEVEL_NONE,
                RESCUE_LEVEL_SCOPED_DEVICE_CONFIG_RESET,
                RESCUE_LEVEL_ALL_DEVICE_CONFIG_RESET,
                RESCUE_LEVEL_WARM_REBOOT,
                RESCUE_LEVEL_RESET_SETTINGS_UNTRUSTED_DEFAULTS,
                RESCUE_LEVEL_RESET_SETTINGS_UNTRUSTED_CHANGES,
                RESCUE_LEVEL_RESET_SETTINGS_TRUSTED_DEFAULTS,
                RESCUE_LEVEL_FACTORY_RESET
            })
    @Retention(RetentionPolicy.SOURCE)
    @interface RescueLevels {}

    @VisibleForTesting static final String TAG = "RescueParty";
    @VisibleForTesting static final long DEFAULT_FACTORY_RESET_THROTTLE_DURATION_MIN = 1440;

    private static final String NAME = "rescue-party-observer";

    private static final String PROP_DISABLE_RESCUE = "persist.sys.disable_rescue";
    private static final String PROP_VIRTUAL_DEVICE = "ro.hardware.virtual_device";
    private static final String PROP_DEVICE_CONFIG_DISABLE_FLAG =
            "persist.device_config.configuration.disable_rescue_party";
    private static final String PROP_DISABLE_FACTORY_RESET_FLAG =
            "persist.device_config.configuration.disable_rescue_party_factory_reset";
    private static final String PROP_THROTTLE_DURATION_MIN_FLAG =
            "persist.device_config.configuration.rescue_party_throttle_duration_min";

    private static final int PERSISTENT_MASK =
            ApplicationInfo.FLAG_PERSISTENT | ApplicationInfo.FLAG_SYSTEM;

    /**
     * EventLog tags used when logging into the event log. Note the values must be sync with
     * frameworks/base/services/core/java/com/android/server/EventLogTags.logtags to get correct
     * name translation.
     */
    private static final int LOG_TAG_RESCUE_SUCCESS = 2902;

    private static final int LOG_TAG_RESCUE_FAILURE = 2903;

    @VisibleForTesting protected static Set<String> sFlagNamespacesToMonitor;

    /**
     * Initialize Rescue Party observer, register it as Package Watchdog's Observer. Also add Device
     * Config listeners for monitoring for required namespaces.
     *
     * <p>TODO: b/354112511 - Have a better name for this method.
     */
    public static void registerHealthObserver(Context context) {
        if (isFlagResetEnabled()) {
            sFlagNamespacesToMonitor = CrashRecoveryUtils.getFlagNamespacesToMonitor();
        }
        RescuePartyObserver observer = RescuePartyObserver.getInstance(context);
        PackageWatchdog.getInstance(context)
                .registerHealthObserver(context.getMainExecutor(), observer);
        if (isFlagResetEnabled()) {
            observer.initializeDeviceConfigMonitoringIfRequiredAsync();
        }
    }

    private static boolean isDisabled() {
        // Check if we're explicitly enabled for testing
        if (SystemProperties.getBoolean(PROP_ENABLE_RESCUE, false)) {
            return false;
        }

        // We're disabled if the DeviceConfig disable flag is set to true.
        // This is in case that an emergency rollback of the feature is needed.
        if (SystemProperties.getBoolean(PROP_DEVICE_CONFIG_DISABLE_FLAG, false)) {
            Slog.v(TAG, "Disabled because of DeviceConfig flag");
            return true;
        }

        // We're disabled on all engineering devices
        if (Build.TYPE.equals("eng")) {
            Slog.v(TAG, "Disabled because of eng build");
            return true;
        }

        // We're disabled on userdebug devices connected over USB, since that's
        // a decent signal that someone is actively trying to debug the device,
        // or that it's in a lab environment.
        if (Build.TYPE.equals("userdebug")) {
            Slog.v(TAG, "Disabled because of userdebug builds");
            return true;
        }

        // One last-ditch check
        if (SystemProperties.getBoolean(PROP_DISABLE_RESCUE, false)) {
            Slog.v(TAG, "Disabled because of manual property");
            return true;
        }

        return false;
    }

    @VisibleForTesting
    protected static boolean isFlagResetEnabled() {
        return Flags.flagResetEnabled() && !Flags.flagResetDisabled();
    }

    /**
     * Check if we're currently attempting to reboot for a factory reset. This method must return
     * true if RescueParty tries to reboot early during a boot loop, since the device will not be
     * fully booted at this time.
     */
    public static boolean isRecoveryTriggeredReboot() {
        return isFactoryResetPropertySet() || isRebootPropertySet();
    }

    static boolean isFactoryResetPropertySet() {
        return CrashRecoveryProperties.attemptingFactoryReset().orElse(false);
    }

    static boolean isRebootPropertySet() {
        return CrashRecoveryProperties.attemptingReboot().orElse(false);
    }

    protected static long getLastFactoryResetTimeMs() {
        return CrashRecoveryProperties.lastFactoryResetTimeMs().orElse(0L);
    }

    protected static int getMaxRescueLevelAttempted() {
        return CrashRecoveryProperties.maxRescueLevelAttempted().orElse(RESCUE_LEVEL_NONE);
    }

    protected static void setFactoryResetProperty(boolean value) {
        CrashRecoveryProperties.attemptingFactoryReset(value);
    }

    protected static void setRebootProperty(boolean value) {
        CrashRecoveryProperties.attemptingReboot(value);
    }

    protected static void setLastFactoryResetTimeMs(long value) {
        CrashRecoveryProperties.lastFactoryResetTimeMs(value);
    }

    protected static void setMaxRescueLevelAttempted(int level) {
        CrashRecoveryProperties.maxRescueLevelAttempted(level);
    }

    @VisibleForTesting
    static long getElapsedRealtime() {
        return SystemClock.elapsedRealtime();
    }

    private static int getMaxRescueLevel() {
        if (!SystemProperties.getBoolean(PROP_DISABLE_FACTORY_RESET_FLAG, false)) {
            return RESCUE_LEVEL_FACTORY_RESET;
        }
        return RESCUE_LEVEL_WARM_REBOOT;
    }

    /**
     * Get the rescue level to perform if this is the n-th attempt at mitigating failure.
     *
     * @param mitigationCount the mitigation attempt number (1 = first attempt etc.).
     * @return the rescue level for the n-th mitigation attempt.
     */
    private static @RescueLevels int getRescueLevel(int mitigationCount) {
        if (mitigationCount == 1) {
            return RESCUE_LEVEL_WARM_REBOOT;
        } else if (mitigationCount >= 2) {
            return Math.min(getMaxRescueLevel(), RESCUE_LEVEL_FACTORY_RESET);
        } else {
            return RESCUE_LEVEL_NONE;
        }
    }

    /**
     * Get the rescue level to perform if this is the n-th attempt at mitigating failure for boot
     * loop.
     *
     * @param mitigationCount the mitigation attempt number (1 = first attempt etc.).
     * @return the rescue level for the n-th mitigation attempt.
     */
    private static @RescueLevels int getRescueLevelForBootLoop(int mitigationCount) {
        if (!isFlagResetEnabled()) {
            return getRescueLevel(mitigationCount);
        }
        if (mitigationCount == 1) {
            return RESCUE_LEVEL_ALL_DEVICE_CONFIG_RESET;
        } else if (mitigationCount == 2) {
            return RESCUE_LEVEL_WARM_REBOOT;
        } else if (mitigationCount >= 3) {
            return Math.min(getMaxRescueLevel(), RESCUE_LEVEL_FACTORY_RESET);
        }
        return RESCUE_LEVEL_NONE;
    }

    private static void executeRescueLevel(
            Context context, @Nullable String failedPackage, int level) {
        Slog.w(TAG, "Attempting rescue level " + levelToString(level));
        try {
            executeRescueLevelInternal(context, level, failedPackage);
            EventLog.writeEvent(LOG_TAG_RESCUE_SUCCESS, level);
            String successMsg = "Finished rescue level " + levelToString(level);
            if (!TextUtils.isEmpty(failedPackage)) {
                successMsg += " for package " + failedPackage;
            }
            logCrashRecoveryEvent(Log.DEBUG, successMsg);
        } catch (Throwable t) {
            logRescueException(level, failedPackage, t);
        }
    }

    private static void executeRescueLevelInternal(
            Context context, @RescueLevels int level, @Nullable String failedPackage) {
        CrashRecoveryStatsLog.write(
                CrashRecoveryStatsLog.RESCUE_PARTY_RESET_REPORTED, level, levelToString(level));
        switch (level) {
            case RESCUE_LEVEL_SCOPED_DEVICE_CONFIG_RESET:
                break;
            case RESCUE_LEVEL_ALL_DEVICE_CONFIG_RESET:
                if (isFlagResetEnabled()) {
                    executeDeviceConfigReset();
                }
                break;
            case RESCUE_LEVEL_WARM_REBOOT:
                executeWarmReboot(context, level, failedPackage);
                break;
            case RESCUE_LEVEL_RESET_SETTINGS_UNTRUSTED_DEFAULTS:
                // do nothing
                break;
            case RESCUE_LEVEL_RESET_SETTINGS_UNTRUSTED_CHANGES:
                // do nothing
                break;
            case RESCUE_LEVEL_RESET_SETTINGS_TRUSTED_DEFAULTS:
                // do nothing
                break;
            case RESCUE_LEVEL_FACTORY_RESET:
                // Before the completion of Reboot, if any crash happens then PackageWatchdog
                // escalates to next level i.e. factory reset, as they happen in separate threads.
                // Adding a check to prevent factory reset to execute before above reboot completes.
                // Note: this reboot property is not persistent resets after reboot is completed.
                if (isRebootPropertySet()) {
                    return;
                }
                executeFactoryReset(context, level, failedPackage);
                break;
        }
    }

    private static void executeDeviceConfigReset() {
        for (String namespace : sFlagNamespacesToMonitor) {
            Slog.w(TAG, "Resetting flags in namespace " + namespace);
            DeviceConfig.resetToDefaults(Settings.RESET_MODE_TRUSTED_DEFAULTS, namespace);
        }
    }

    private static void executeWarmReboot(
            Context context, int level, @Nullable String failedPackage) {
        if (shouldThrottleReboot()) {
            return;
        }

        // Request the reboot from a separate thread to avoid deadlock on PackageWatchdog
        // when device shutting down.
        setRebootProperty(true);

        if (Flags.synchronousRebootInRescueParty()) {
            try {
                PowerManager pm = context.getSystemService(PowerManager.class);
                if (pm != null) {
                    pm.reboot(TAG);
                }
            } catch (Throwable t) {
                logRescueException(level, failedPackage, t);
            }
        } else {
            Runnable runnable =
                    () -> {
                        try {
                            PowerManager pm = context.getSystemService(PowerManager.class);
                            if (pm != null) {
                                pm.reboot(TAG);
                            }
                        } catch (Throwable t) {
                            logRescueException(level, failedPackage, t);
                        }
                    };
            Thread thread = new Thread(runnable);
            thread.start();
        }
    }

    private static void executeFactoryReset(
            Context context, int level, @Nullable String failedPackage) {
        if (shouldThrottleReboot()) {
            return;
        }
        setFactoryResetProperty(true);
        long now = System.currentTimeMillis();
        setLastFactoryResetTimeMs(now);

        if (Flags.synchronousRebootInRescueParty()) {
            try {
                RecoverySystem.rebootPromptAndWipeUserData(context, TAG + "," + failedPackage);
            } catch (Throwable t) {
                logRescueException(level, failedPackage, t);
            }
        } else {
            Runnable runnable =
                    new Runnable() {
                        @Override
                        public void run() {
                            try {
                                RecoverySystem.rebootPromptAndWipeUserData(
                                        context, TAG + "," + failedPackage);
                            } catch (Throwable t) {
                                logRescueException(level, failedPackage, t);
                            }
                        }
                    };
            Thread thread = new Thread(runnable);
            thread.start();
        }
    }

    private static String getCompleteMessage(Throwable t) {
        final StringBuilder builder = new StringBuilder();
        builder.append(t.getMessage());
        while ((t = t.getCause()) != null) {
            builder.append(": ").append(t.getMessage());
        }
        return builder.toString();
    }

    private static void logRescueException(
            int level, @Nullable String failedPackageName, Throwable t) {
        final String msg = getCompleteMessage(t);
        EventLog.writeEvent(LOG_TAG_RESCUE_FAILURE, level, msg);
        String failureMsg = "Failed rescue level " + levelToString(level);
        if (!TextUtils.isEmpty(failedPackageName)) {
            failureMsg += " for package " + failedPackageName;
        }
        logCrashRecoveryEvent(Log.ERROR, failureMsg + ": " + msg);
    }

    private static int mapRescueLevelToUserImpact(int rescueLevel) {
        switch (rescueLevel) {
            case RESCUE_LEVEL_SCOPED_DEVICE_CONFIG_RESET:
                return PackageHealthObserverImpact.USER_IMPACT_LEVEL_10;
            case RESCUE_LEVEL_ALL_DEVICE_CONFIG_RESET:
                return PackageHealthObserverImpact.USER_IMPACT_LEVEL_40;
            case RESCUE_LEVEL_WARM_REBOOT:
                return PackageHealthObserverImpact.USER_IMPACT_LEVEL_50;
            case RESCUE_LEVEL_RESET_SETTINGS_UNTRUSTED_DEFAULTS:
                return PackageHealthObserverImpact.USER_IMPACT_LEVEL_71;
            case RESCUE_LEVEL_RESET_SETTINGS_UNTRUSTED_CHANGES:
                return PackageHealthObserverImpact.USER_IMPACT_LEVEL_75;
            case RESCUE_LEVEL_RESET_SETTINGS_TRUSTED_DEFAULTS:
                return PackageHealthObserverImpact.USER_IMPACT_LEVEL_80;
            case RESCUE_LEVEL_FACTORY_RESET:
                return PackageHealthObserverImpact.USER_IMPACT_LEVEL_100;
            default:
                return PackageHealthObserverImpact.USER_IMPACT_LEVEL_0;
        }
    }

    /**
     * Handle mitigation action for package failures. This observer will be register to Package
     * Watchdog and will receive calls about package failures. This observer is persistent so it may
     * choose to mitigate failures for packages it has not explicitly asked to observe.
     */
    public static class RescuePartyObserver implements PackageHealthObserver {

        @VisibleForTesting
        protected static final long DEFAULT_OBSERVING_DURATION_MS = TimeUnit.DAYS.toMillis(1);

        @VisibleForTesting
        protected static final long DEFAULT_HEALTH_CHECK_TRIGGER_DELAY_MS =
                TimeUnit.MINUTES.toMillis(5);

        private final Context mContext;
        private final Executor mExecutor;
        private final Runnable mTriggerHealthCheckRunnable = this::performHealthCheck;
        private List<String> mNetworkStackPackages;
        @VisibleForTesting protected final Handler mHandler;

        @GuardedBy("RescuePartyObserver.class")
        static RescuePartyObserver sRescuePartyObserver;

        private RescuePartyObserver(Context context) {
            mContext = context;

            if (isFlagResetEnabled()) {
                HandlerThread handlerThread = new HandlerThread("RescuePartyObserver");
                handlerThread.start();
                mHandler = new Handler(handlerThread.getLooper());
                mExecutor = new HandlerExecutor(mHandler);
                String networkPackageName = CrashRecoveryUtils.getNetworkStackPackageName(mContext);
                if (networkPackageName != null) {
                    mNetworkStackPackages = Collections.singletonList(networkPackageName);
                } else {
                    Slog.wtf(TAG, "Unable to find NetworkPackage for monitoring network health");
                }
            } else {
                mHandler = null;
                mExecutor = null;
            }
        }

        /** Creates or gets singleton instance of RescueParty. */
        public static RescuePartyObserver getInstance(Context context) {
            synchronized (RescuePartyObserver.class) {
                if (sRescuePartyObserver == null) {
                    sRescuePartyObserver = new RescuePartyObserver(context);
                }
                return sRescuePartyObserver;
            }
        }

        @VisibleForTesting
        static void reset() {
            synchronized (RescuePartyObserver.class) {
                sRescuePartyObserver = null;
            }
        }

        @Override
        public int onHealthCheckFailed(
                @Nullable VersionedPackage failedPackage,
                @FailureReasons int failureReason,
                int mitigationCount) {
            int impact = PackageHealthObserverImpact.USER_IMPACT_LEVEL_0;
            if (!isDisabled()
                    && (failureReason == PackageWatchdog.FAILURE_REASON_APP_CRASH
                            || failureReason
                                    == PackageWatchdog.FAILURE_REASON_APP_NOT_RESPONDING)) {
                impact = mapRescueLevelToUserImpact(getRescueLevel(mitigationCount));
            }

            Slog.i(
                    TAG,
                    "Checking available remediations for health check failure."
                            + " failedPackage: "
                            + (failedPackage == null ? null : failedPackage.getPackageName())
                            + " failureReason: "
                            + failureReason
                            + " available impact: "
                            + impact);
            return impact;
        }

        @Override
        public int onExecuteHealthCheckMitigation(
                @Nullable VersionedPackage failedPackage,
                @FailureReasons int failureReason,
                int mitigationCount) {
            if (isDisabled()) {
                return MITIGATION_RESULT_SKIPPED;
            }
            Slog.i(
                    TAG,
                    "Executing remediation."
                            + " failedPackage: "
                            + (failedPackage == null ? null : failedPackage.getPackageName())
                            + " failureReason: "
                            + failureReason
                            + " mitigationCount: "
                            + mitigationCount);
            if (failureReason == PackageWatchdog.FAILURE_REASON_APP_CRASH
                    || failureReason == PackageWatchdog.FAILURE_REASON_APP_NOT_RESPONDING) {
                final int level;
                level = getRescueLevel(mitigationCount);
                executeRescueLevel(
                        mContext,
                        failedPackage == null ? null : failedPackage.getPackageName(),
                        level);
                return MITIGATION_RESULT_SUCCESS;
            } else if (failureReason == PackageWatchdog.FAILURE_REASON_EXPLICIT_HEALTH_CHECK) {
                if (isFlagResetEnabled()) {
                    executeDeviceConfigReset();
                    return MITIGATION_RESULT_SUCCESS;
                }
            }
            return MITIGATION_RESULT_SKIPPED;
        }

        @Override
        public boolean isPersistent() {
            return true;
        }

        @Override
        public boolean mayObservePackage(@NonNull String packageName) {
            PackageManager pm = mContext.getPackageManager();
            try {
                // A package is a module if this is non-null
                if (pm.getModuleInfo(packageName, 0) != null) {
                    return true;
                }
            } catch (PackageManager.NameNotFoundException | IllegalStateException ignore) {
            }

            return isPersistentSystemApp(packageName);
        }

        @Override
        public int onBootLoop(int mitigationCount) {
            if (isDisabled()) {
                return PackageHealthObserverImpact.USER_IMPACT_LEVEL_0;
            }
            return mapRescueLevelToUserImpact(getRescueLevelForBootLoop(mitigationCount));
        }

        @Override
        public int onExecuteBootLoopMitigation(int mitigationCount) {
            if (isDisabled()) {
                return MITIGATION_RESULT_SKIPPED;
            }
            final int level;
            level = getRescueLevelForBootLoop(mitigationCount);
            executeRescueLevel(mContext, /* failedPackage= */ null, level);
            return MITIGATION_RESULT_SUCCESS;
        }

        @Override
        public String getUniqueIdentifier() {
            return NAME;
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

        /**
         * Asynchronously start monitoring for device config flag updates if network stack has been
         * found.
         */
        public void initializeDeviceConfigMonitoringIfRequiredAsync() {
            // no need to initialize if we couldn't find network package.
            if (mNetworkStackPackages == null) {
                return;
            }
            mHandler.post(this::initializeDeviceConfigMonitoring);
        }

        /** Start monitoring device config for flag updates */
        @VisibleForTesting
        protected void initializeDeviceConfigMonitoring() {
            for (String namespace : sFlagNamespacesToMonitor) {
                DeviceConfig.addOnPropertiesChangedListener(
                        namespace, mExecutor, this::onPropertiesUpdated);
            }
        }

        /** Triggers explicit health check. */
        private void performHealthCheck() {
            PackageWatchdog.getInstance(mContext)
                    .startExplicitHealthCheck(
                            mNetworkStackPackages, DEFAULT_OBSERVING_DURATION_MS, this);
        }

        /** Trigger delayed network health check to optimize for bulk update */
        private void onPropertiesUpdated(DeviceConfig.Properties properties) {
            mHandler.removeCallbacks(mTriggerHealthCheckRunnable);
            mHandler.postDelayed(
                    mTriggerHealthCheckRunnable, DEFAULT_HEALTH_CHECK_TRIGGER_DELAY_MS);
        }
    }

    /**
     * Returns {@code true} if Rescue Party is allowed to attempt a reboot or factory reset. Will
     * return {@code false} if a factory reset was already offered recently.
     */
    private static boolean shouldThrottleReboot() {
        Long lastResetTime = getLastFactoryResetTimeMs();
        long now = System.currentTimeMillis();
        long throttleDurationMin =
                SystemProperties.getLong(
                        PROP_THROTTLE_DURATION_MIN_FLAG,
                        DEFAULT_FACTORY_RESET_THROTTLE_DURATION_MIN);
        return now < lastResetTime + TimeUnit.MINUTES.toMillis(throttleDurationMin);
    }

    /**
     * Hacky test to check if the device has an active USB connection, which is a good proxy for
     * someone doing local development work.
     */
    private static boolean isUsbActive() {
        if (SystemProperties.getBoolean(PROP_VIRTUAL_DEVICE, false)) {
            Slog.v(TAG, "Assuming virtual device is connected over USB");
            return true;
        }
        try {
            final String state =
                    FileUtils.readTextFile(
                            new File("/sys/class/android_usb/android0/state"), 128, "");
            return "CONFIGURED".equals(state.trim());
        } catch (Throwable t) {
            Slog.w(TAG, "Failed to determine if device was on USB", t);
            return false;
        }
    }

    private static String levelToString(int level) {
        switch (level) {
            case RESCUE_LEVEL_NONE:
                return "NONE";
            case RESCUE_LEVEL_SCOPED_DEVICE_CONFIG_RESET:
                return "SCOPED_DEVICE_CONFIG_RESET";
            case RESCUE_LEVEL_ALL_DEVICE_CONFIG_RESET:
                return "ALL_DEVICE_CONFIG_RESET";
            case RESCUE_LEVEL_WARM_REBOOT:
                return "WARM_REBOOT";
            case RESCUE_LEVEL_RESET_SETTINGS_UNTRUSTED_DEFAULTS:
                return "RESET_SETTINGS_UNTRUSTED_DEFAULTS";
            case RESCUE_LEVEL_RESET_SETTINGS_UNTRUSTED_CHANGES:
                return "RESET_SETTINGS_UNTRUSTED_CHANGES";
            case RESCUE_LEVEL_RESET_SETTINGS_TRUSTED_DEFAULTS:
                return "RESET_SETTINGS_TRUSTED_DEFAULTS";
            case RESCUE_LEVEL_FACTORY_RESET:
                return "FACTORY_RESET";
            default:
                return Integer.toString(level);
        }
    }
}
