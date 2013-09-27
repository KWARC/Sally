using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Office.Tools.Ribbon;
using System.Windows.Forms;
using System.Net.Sockets;
using System.Runtime.InteropServices;
using Excel = Microsoft.Office.Interop.Excel;
using System.Net;
using Microsoft.Office.Core;
using System.IO;
using System.Diagnostics;
using Google.ProtocolBuffers;
using Cometd.Client;
using Cometd.Client.Transport;
using Cometd.Bayeux;
using Cometd.Bayeux.Client;
using Cometd.Common;
using sally;
using System.Reflection;
using System.Collections;
using System.Xml.Linq;
//using ExcelDna;
//using ExcelWrapper;

namespace ExcelAddIn1
{
    class CurrentSpreadSheet
    {
        private Excel.Worksheet _currentWorkSheet = null;
        private Excel.Workbook _currentWorkBook = null;
        //private Excel.Application _currentApplication = null;
        private Excel.Range _currentRange = null;

        private String _currentfilename;
        //public static HashSet<Excel.Workbook> currentWorkBooks = new HashSet<Excel.Workbook>();


        //public Excel.Application CurrentApplication { get; set; }
        public String CurrentFilename { get { return _currentfilename; } set { _currentfilename = value; } }
        public Excel.Workbook CurrentWorkBook { get { return _currentWorkBook; } set { _currentWorkBook = value; } }
        public Excel.Worksheet CurrentWorkSheet { get { return _currentWorkSheet; } set {_currentWorkSheet = value; } }
        public Excel.Range CurrentRange { get { return _currentRange; } set { _currentRange = value; } }
        //public static HashSet<Excel.Workbook> CurrentWorkBooks { get; set; }


        private static CurrentSpreadSheet instance;

        public static CurrentSpreadSheet Instance
        {
            get
            {
                if (instance == null)
                {
                    instance = new CurrentSpreadSheet();
                }
                return instance;
            }
        }


        //public CurrentSpreadSheet()
        //{
        //    try
        //    {
        //        this.CurrentApplication = (Excel.Application)ExcelDna.Integration.ExcelDnaUtil.Application;
        //        //this.CurrentApplication = (Excel.Application)Globals.ThisAddIn.Application;

        //    }
        //    catch (NullReferenceException)
        //    {
        //        MessageBox.Show("DEBUG: Excel application object not registered. Trying plan B..");

        //        //Getting Excel's application object instance
        //        int iSection = 0, iTries = 0;

        //    tryAgain:
        //        try
        //        {
        //            iSection = 1; //Attempting GetActiveObject
        //            this.CurrentApplication = (Excel.Application)Marshal.GetActiveObject("Excel.Application");
        //            iSection = 0; //GetActiveObject succeeded so resume or go for normal error handling if needed
        //            this.CurrentApplication.Visible = true;
        //        }
        //        catch (Exception err)
        //        {
        //            System.Console.WriteLine("Visual C# .NET Error Attaching to Running Instance of Office Application .. yet.");
        //            if (iSection == 1)
        //            {
        //                //GetObject may have failed because the
        //                //Shell function is asynchronous; enough time has not elapsed
        //                //for GetObject to find the running Office application. Wait
        //                //1/2 seconds and retry the GetObject. If we try 20 times
        //                //and GetObject still fails, we assume some other reason
        //                //for GetObject failing and exit the procedure.
        //                iTries++;
        //                if (iTries < 30)
        //                { 
        //                    System.Threading.Thread.Sleep(500); // Wait 1/2 seconds.
        //                    goto tryAgain; //resume code at the GetObject line
        //                }
        //                else
        //                {
        //                    MessageBox.Show("GetObject still failing.  Process ended.");
        //                }

        //            }
        //            else
        //            {
        //                //iSection == 0 so normal error handling
        //                MessageBox.Show(err.Message);
        //            }
        //        }
        //    }

        //    //MessageBox.Show("Application: " + this.CurrentApplication.ToString());
        //}

        public void updateCurrentSpreadSheet(Excel.Workbook Wb)
        {
            try
            {
                this.CurrentWorkBook = Wb;
                this.CurrentWorkSheet = Wb.ActiveSheet;
                Globals.ThisAddIn.Application.StatusBar = "Alex's Workbook: " + Wb.Name + ".";
            }
            catch (Exception)
            {
                MessageBox.Show("Workbook not available or something like that.");
            }
            //MessageBox.Show("Workbook " + Wb.Name + " registered.");
        }

        public void updateCurrentSpreadSheet() {

            try
            {
                this.CurrentWorkSheet = this.CurrentWorkBook.ActiveSheet;
                Globals.ThisAddIn.Application.StatusBar = "Alex's Worksheet: " + this.CurrentWorkSheet.Name + ".";
            }
            catch (Exception)
            {
                Globals.ThisAddIn.Application.StatusBar ="Alex sees emptiness.";
            }
            
            
        }
        


    }
}



        //public void updateCurrentSpreadSheet()
        //{
        //    try
        //    {
        //        //this.CurrentWorkBook = (Excel.Workbook)this.CurrentApplication.ActiveWorkbook;
        //        this.CurrentWorkBook = (Excel.Workbook)Globals.ThisAddIn.Application.ActiveWorkbook;
        //    }
        //    catch (NullReferenceException err)
        //    {
        //        MessageBox.Show("No workbook is active. " + err.Message);
        //    }


        //    try
        //    {
        //        //this.CurrentWorkSheet = ((Excel.Worksheet)this.CurrentWorkBook.ActiveSheet);
        //        this.CurrentWorkSheet = (Excel.Worksheet)Globals.ThisAddIn.Application.ActiveSheet;
        //        MessageBox.Show("Current Worksheet Updated.");

        //    }
        //    catch (NullReferenceException err)
        //    {
        //        MessageBox.Show("No sheet is active. " + err.Message);
        //    }
        //    catch (InvalidCastException)
        //    {
        //        //do nothing for now
        //    }
        //}
