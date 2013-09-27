using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Office.Tools.Ribbon;
using System.Windows.Forms;
using System.Net.Sockets;
using System.Runtime.InteropServices;
using Microsoft.Office.Interop.Excel;

namespace ExcelAddIn1
{
    public partial class Ribbon1
    {
        Worksheet _sheet;
        public double pppx = -1, pppy = -1;
        public double fbTop = -1, fbLeft = -1;
        public double hLeft = -1, hTop = -1;
        public bool init = false;

        const int LOGPIXELSX = 88;
        const int LOGPIXELSY = 90;
        [DllImport("user32.dll")]
        static extern IntPtr GetDC(IntPtr hWnd);
        [DllImport("user32.dll")]
        static extern bool ReleaseDC(IntPtr hWnd, IntPtr hDC);
        [DllImport("gdi32.dll")]
        static extern int GetDeviceCaps(IntPtr hdc, int nIndex);

        private void PixelsPerPointX()
        {
            if (!this.init)
            {
                IntPtr hdc = GetDC(new IntPtr(0));
                int PixPerInchX = GetDeviceCaps(hdc, LOGPIXELSX);
                double pppx = PixPerInchX / 72.0; //72 is the points per inch
                ReleaseDC(new IntPtr(0), hdc);
                this.pppx = pppx;
            }
        }

        private void PixelsPerPointY()
        {
            if (!this.init)
            {
                IntPtr hdc = GetDC(new IntPtr(0));
                int PixPerInchY = GetDeviceCaps(hdc, LOGPIXELSY);
                double pppy = PixPerInchY / 72.0; //72 is the points per inch            
                ReleaseDC(new IntPtr(0), hdc);
                this.pppy = pppy;
            }
        }

        private void GetFormulaBarAndHeadingsDim()
        {
            if (!this.init)
            {
                bool formBar = Globals.ThisAddIn.Application.DisplayFormulaBar;
                bool headings = Globals.ThisAddIn.Application.ActiveWindow.DisplayHeadings;
                double beforeH, afterH, beforeW, afterW;

                //check the size of the formula bar                
                beforeH = Globals.ThisAddIn.Application.ActiveWindow.Height;
                beforeW = Globals.ThisAddIn.Application.ActiveWindow.Width;
                Globals.ThisAddIn.Application.DisplayFormulaBar = false;
                afterH = Globals.ThisAddIn.Application.ActiveWindow.Height;
                afterW = Globals.ThisAddIn.Application.ActiveWindow.Width;                
                Globals.ThisAddIn.Application.DisplayFormulaBar = true;                
                this.fbLeft = afterW - beforeW;
                this.fbTop = afterH - beforeH;



                this.hLeft = 0;
                this.hTop = 0;

                Globals.ThisAddIn.Application.DisplayFormulaBar = formBar;
                Globals.ThisAddIn.Application.ActiveWindow.DisplayHeadings = headings;
            }
        }

        private void log(String s)
        {
            this.label3.Label += s + " | ";
        }

        private void Ribbon1_Load(object sender, RibbonUIEventArgs e)
        {            
            this._sheet = Globals.ThisAddIn.Application.ActiveSheet;
            this._sheet.SelectionChange +=new DocEvents_SelectionChangeEventHandler(sheet_SelectionChange);
        }

        private void sheet_SelectionChange(Range rng)
        {
            MessageBox.Show("Select changed!");
        }


        private void CellTopLeftPixels(Range rng)
        {
            if (!init)
            {
                PixelsPerPointX();
                PixelsPerPointY();
                GetFormulaBarAndHeadingsDim();
                init = true;
            }

            double appTop = Globals.ThisAddIn.Application.Top;
            double appLeft = Globals.ThisAddIn.Application.Left;
            long RibbonHeight = Globals.ThisAddIn.Application.CommandBars["Ribbon"].Height;
            

            this.log("aT " + appTop);
            this.log("aL " + appLeft);
            this.log("rH " + RibbonHeight);
            this.log("px " + this.pppx);
            this.log("py " + this.pppy);
            this.log("fY " + this.fbTop);
            this.log("fX " + this.fbLeft);
            this.log("hY " + this.hTop);
            this.log("hX " + this.hLeft);
            this.log("rT " + rng.Top);
            this.log("rL " + rng.Left);
            this.log("1T " + (appTop + RibbonHeight + rng.Top + this.fbTop + this.hTop));
            this.log("1L " + (appLeft + rng.Left + this.fbLeft + this.hTop));


            long top = (long)((appTop + RibbonHeight + rng.Top + this.fbTop + this.hTop) * this.pppy);
            long left = (long)((appLeft + rng.Left + this.fbLeft + this.hLeft) * this.pppx);
            this.label1.Label = "left: " + left + " top: " + top;


            long topc = (long)((appTop + RibbonHeight + rng.Top + this.fbTop + this.hTop + rng.Height) * pppy);
            long leftc = (long)((appLeft + rng.Left + rng.Width + this.fbLeft + this.hTop) * pppx);
            this.label2.Label = "left: " + leftc + " top: " + topc;
        }

        private void button1_Click(object sender, RibbonControlEventArgs e)
        {
            this.label3.Label = "";
            CellTopLeftPixels(Globals.ThisAddIn.Application.ActiveCell);
        }        
    }
}
