/*
 * Copyright (C) 2024 The Android Open Source Project
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

package com.android.server.crashrecovery;

import static android.aconfig.Aconfig.flag_metadata.flag_storage_backend.DEVICE_CONFIG;

import android.aconfig.Aconfig.parsed_flag;
import android.aconfig.Aconfig.parsed_flags;
import android.annotation.Nullable;
import android.content.ComponentName;
import android.content.Context;
import android.content.Intent;
import android.content.pm.ApplicationInfo;
import android.content.pm.PackageManager;
import android.content.pm.ResolveInfo;
import android.os.Environment;
import android.util.FileUtils;
import android.util.IndentingPrintWriter;
import android.util.Log;
import android.util.Slog;
import android.util.SparseArray;

import com.android.internal.annotations.VisibleForTesting;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.time.LocalDateTime;
import java.time.ZoneId;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Class containing helper methods for the CrashRecoveryModule.
 *
 * @hide
 */
public class CrashRecoveryUtils {
    private static final String TAG = "CrashRecoveryUtils";
    private static final long MAX_CRITICAL_INFO_DUMP_SIZE = 1000 * 1000; // ~1MB
    private static final String APEX_ACONFIG_PATH_SUFFIX = "/etc/aconfig_flags.pb";
    private static final Object sFileLock = new Object();
    private static Set<String> sApkNamespaces =
            Set.of("com_android_networkstack", "com_android_captiveportallogin");

    @VisibleForTesting
    protected static final String NETWORK_STACK_CONNECTOR_CLASS =
            "android.net.INetworkStackConnector";

    @VisibleForTesting protected static String sApexDir = "/apex";

    /** Persist recovery related events in crashrecovery events file.**/
    public static void logCrashRecoveryEvent(int priority, String msg) {
        Log.println(priority, TAG, msg);
        try {
            File fname = getCrashRecoveryEventsFile();
            synchronized (sFileLock) {
                FileOutputStream out = new FileOutputStream(fname, true);
                PrintWriter pw = new PrintWriter(out);
                String dateString = LocalDateTime.now(ZoneId.systemDefault()).toString();
                pw.println(dateString + ": " + msg);
                pw.close();
            }
        } catch (IOException e) {
            Log.e(TAG, "Unable to log CrashRecoveryEvents " + e.getMessage());
        }
    }

    /** Dump recovery related events from crashrecovery events file.**/
    public static void dumpCrashRecoveryEvents(IndentingPrintWriter pw) {
        pw.println("CrashRecovery Events: ");
        pw.increaseIndent();
        final File file = getCrashRecoveryEventsFile();
        final long skipSize = file.length() - MAX_CRITICAL_INFO_DUMP_SIZE;
        synchronized (sFileLock) {
            try (BufferedReader in = new BufferedReader(new FileReader(file))) {
                if (skipSize > 0) {
                    in.skip(skipSize);
                }
                String line;
                while ((line = in.readLine()) != null) {
                    pw.println(line);
                }
            } catch (IOException e) {
                Log.e(TAG, "Unable to dump CrashRecoveryEvents " + e.getMessage());
            }
        }
        pw.decreaseIndent();
    }

    private static File getCrashRecoveryEventsFile() {
        File systemDir = new File(Environment.getDataDirectory(), "system");
        return new File(systemDir, "crashrecovery-events.txt");
    }

    /** Append "key,value" into designated file **/
    public static void putKeyValue(File file, int key, String value) {
        try {
            FileOutputStream fos = new FileOutputStream(file, true);
            PrintWriter pw = new PrintWriter(fos);
            pw.append(String.valueOf(key)).append(",").append(value);
            pw.println();
            pw.flush();
            FileUtils.sync(fos);
            pw.close();
        } catch (IOException e) {
            Log.e(TAG, String.format("Failed to save id %s, value %s into %s", key, value,
                    file.getAbsolutePath()), e);
            file.delete();
        }
    }

    /** Overwrite the content of designated file with input keyValues **/
    public static void writeAllKeyValues(File file, SparseArray<String> keyValues) {
        StringBuilder content = new StringBuilder();
        for (int i = 0; i < keyValues.size(); i++) {
            int key = keyValues.keyAt(i);
            String value = keyValues.get(key);
            content.append(key).append(",").append(value).append(System.lineSeparator());
        }

        try (FileOutputStream fos = new FileOutputStream(file)) {
            fos.write(content.toString().getBytes());
        } catch (IOException e) {
            Log.e(TAG, String.format("Failed to write %s", file.getAbsolutePath()), e);
            file.delete();
        }
    }

    public static SparseArray<String> readAllKeyValues(File file) {
        SparseArray<String> result = new SparseArray<>();
        try (BufferedReader reader = new BufferedReader(new FileReader(file))) {
            String line;
            while ((line = reader.readLine()) != null) {
                // Each line is of the format: "id,value"
                String[] values = line.trim().split(",");
                String key = values[0];
                String value = "";
                if (values.length > 1) {
                    value = values[1];
                }
                result.put(Integer.parseInt(key), value);
            }
        } catch (Exception ignore) {
            return new SparseArray<>();
        }
        return result;
    }

    /**
     * Scans APEX directory for aconfig_flags.pb files and extracts namespaces from them. Currently
     * the APK namespaces are hardcoded.
     *
     * @return A Set of aconfig namespaces strings present in apexes.
     */
    public static Set<String> getFlagNamespacesInModules() {
        Set<String> moduleNamespaces = new HashSet<>();
        moduleNamespaces.addAll(sApkNamespaces);
        List<String> apexProtoPaths = getApexProtoPaths();
        for (String fileName : apexProtoPaths) {
            try (FileInputStream inputStream = new FileInputStream(fileName)) {
                Set<String> namespaces =
                        parseAconfigNamespacesWithDeviceConfigStorage(inputStream.readAllBytes());
                moduleNamespaces.addAll(namespaces);
            } catch (IOException e) {
                Slog.e(TAG, "failed to read protobuf", e);
            }
        }
        return moduleNamespaces;
    }

    private static List<String> getApexProtoPaths() {
        ArrayList<String> paths = new ArrayList<>();

        File apexDirectory = new File(sApexDir);
        if (!apexDirectory.isDirectory()) {
            return paths;
        }

        File[] subdirs = apexDirectory.listFiles();
        if (subdirs == null) {
            return paths;
        }

        for (File prefix : subdirs) {
            // For each mainline modules, there are two directories, one <modulepackage>/,
            // and one <modulepackage>@<versioncode>/. Just read the former.
            if (prefix.getName().contains("@")) {
                continue;
            }

            File protoPath = new File(prefix, APEX_ACONFIG_PATH_SUFFIX);
            if (!protoPath.exists()) {
                continue;
            }
            paths.add(protoPath.getAbsolutePath());
        }
        return paths;
    }

    private static Set<String> parseAconfigNamespacesWithDeviceConfigStorage(byte[] fileContents) {
        Set<String> namespaces = new HashSet<>();
        try {
            parsed_flags parsedFlags = parsed_flags.parseFrom(fileContents);
            for (parsed_flag flag : parsedFlags.getParsedFlagList()) {
                if (DEVICE_CONFIG.equals(flag.getMetadata().getStorage())) {
                    namespaces.add(flag.getNamespace());
                }
            }
        } catch (IOException e) {
            Slog.e(TAG, "failed to parse protobuf", e);
        }
        return namespaces;
    }

    /**
     * Finds network service using network stack connector class to get it's package name.
     *
     * @return network stack package name if found
     */
    @Nullable
    public static String getNetworkStackPackageName(Context context) {
        Intent intent = new Intent(NETWORK_STACK_CONNECTOR_CLASS);
        ComponentName comp = resolveSystemService(intent, context.getPackageManager());
        if (comp == null) {
            return null;
        }
        return comp.getPackageName();
    }

    private static ComponentName resolveSystemService(Intent intent, PackageManager pm) {
        List<ResolveInfo> results = pm.queryIntentServices(intent, 0);
        ComponentName comp = null;
        for (int i = 0; i < results.size(); i++) {
            ResolveInfo ri = results.get(i);
            if ((ri.serviceInfo.applicationInfo.flags & ApplicationInfo.FLAG_SYSTEM) == 0) {
                continue;
            }
            ComponentName foundComp =
                    new ComponentName(
                            ri.serviceInfo.applicationInfo.packageName, ri.serviceInfo.name);
            if (comp != null) {
                Slog.wtf(TAG, "Multiple system services to handle: " + comp + ", " + foundComp);
                return null;
            }
            comp = foundComp;
        }
        return comp;
    }
}
