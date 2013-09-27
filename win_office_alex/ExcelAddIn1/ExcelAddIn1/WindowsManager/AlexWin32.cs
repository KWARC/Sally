using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;

namespace ExcelAddIn1.WindowsManager
{
    public class AlexWin32
    {
        //moved to TheoFx. Alex may also need one in the future


        [DllImport("user32.dll")]
        static extern int SetForegroundWindow(IntPtr hWnd);

        [DllImport("user32.dll")]
        static extern int FindWindow(String className, String windowName);


       public static void bringToFront(string processName, string windowsTitle)
        {
            Process[] processes = Process.GetProcessesByName(processName);
            foreach (Process p in processes)
            {
                if (p.MainWindowTitle.Contains(windowsTitle))
                {
                    SetForegroundWindow(p.MainWindowHandle);
                }
            }

        }

    }
}
