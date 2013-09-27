using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Runtime.InteropServices;
using Microsoft.Office.Interop.Excel;

namespace ExcelAddIn1
{

    static class Display
    {
        private static double pppx = -1, pppy = -1; //points per pixel per axis
        private static double fbTop = -1, fbLeft = -1; //formula bar size (height + width)
        private static double hLeft = -1, hTop = -1; //headings size (height and width)
        private static bool init = false;
        public static double top = 0, left = 0;

        const int LOGPIXELSX = 88; //magic numbers. See http://stackoverflow.com/questions/9246921/excel-addin-cell-absolute-position/9249961 for more details
        const int LOGPIXELSY = 90;
        [DllImport("user32.dll")]
        static extern IntPtr GetDC(IntPtr hWnd);
        [DllImport("user32.dll")]
        static extern bool ReleaseDC(IntPtr hWnd, IntPtr hDC);
        [DllImport("gdi32.dll")]
        static extern int GetDeviceCaps(IntPtr hdc, int nIndex);


        private static void PixelsPerPointX()
        {
            if (!init)
            {
                IntPtr hdc = GetDC(new IntPtr(0));
                int PixPerInchX = GetDeviceCaps(hdc, LOGPIXELSX);
                double pppx1 = PixPerInchX / 72.0; //72 is the points per inch
                ReleaseDC(new IntPtr(0), hdc);
                pppx = pppx1;
            }
        }

        private static void PixelsPerPointY()
        {
            if (!init)
            {
                IntPtr hdc = GetDC(new IntPtr(0));
                int PixPerInchY = GetDeviceCaps(hdc, LOGPIXELSY);
                double pppy1 = PixPerInchY / 72.0; //72 is the points per inch            
                ReleaseDC(new IntPtr(0), hdc);
                pppy = pppy1;
            }
        }

        private static void GetFormulaBarAndHeadingsDim()
        {
            if (!init)
            {
                //save the user settings
                bool formBar = Globals.ThisAddIn.Application.DisplayFormulaBar;
                bool headings = Globals.ThisAddIn.Application.ActiveWindow.DisplayHeadings;
                double beforeH, afterH, beforeW, afterW;

                //check the size of the formula bar: make it visible, measure, make it invisible, measure, difference
                Globals.ThisAddIn.Application.DisplayFormulaBar = true;
                beforeH = Globals.ThisAddIn.Application.ActiveWindow.Height;
                beforeW = Globals.ThisAddIn.Application.ActiveWindow.Width;
                Globals.ThisAddIn.Application.DisplayFormulaBar = false;
                afterH = Globals.ThisAddIn.Application.ActiveWindow.Height;
                afterW = Globals.ThisAddIn.Application.ActiveWindow.Width;

                fbLeft = afterW - beforeW;
                fbTop = afterH - beforeH;


                //don't know how to find out the sizes: Window.Height and Window.UsableHeight both return same values
                // when the headings are shown or not shown.
                hLeft = 0;
                hTop = 0;


                //restore user settings
                Globals.ThisAddIn.Application.DisplayFormulaBar = formBar;
                Globals.ThisAddIn.Application.ActiveWindow.DisplayHeadings = headings;
            }
        }
        static void write(string bla)
        {
            System.DateTime currentDateTime = System.DateTime.Now;
            string dateStamp = currentDateTime.ToString("dMMMMyyyy_hh.mm.ss");

            string fileName = System.Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments) + "\\\\" + dateStamp + ".txt";
            System.IO.StreamWriter sw = new System.IO.StreamWriter(fileName);
            sw.WriteLine(bla);
            sw.Close();
        }
        public static void CellTopLeftPixels(Range rng)
        {
            if (!init)
            {
                PixelsPerPointX();
                PixelsPerPointY();
                GetFormulaBarAndHeadingsDim();
                init = true;
            }

            //get all the pieces together
                
            double appTop = Globals.ThisAddIn.Application.Top;
            double appLeft = Globals.ThisAddIn.Application.Left;
            long RibbonHeight = Globals.ThisAddIn.Application.CommandBars["Ribbon"].Height;


            //the upper-left corner position
            
            top = (long)((appTop + RibbonHeight + rng.Top + fbTop + hTop - 15) * pppy);
            left = (long)((appLeft + rng.Left + fbLeft + hLeft + rng.Width + 25) * pppx);
           

         
            //the lower-right corner position
            long topc = (long)((appTop + RibbonHeight + rng.Top + fbTop + hTop + rng.Height) * pppy);
            long leftc = (long)((appLeft + rng.Left + rng.Width + fbLeft + hTop) * pppx);
            
        }
    }
}
