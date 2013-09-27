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
//using ExcelWrapper;


namespace ExcelAddIn1
{
    class TestCurrentSpreadSheet
    {
        //Refactored + new codes (test) are mostly down here >>>>>>>>>>>>>> START <<<<<<<<<<<<<<<<<<<<<<<
        //Still need the event listeners
        //Finding: can get the active sheet with this code : this.CurrentWorkSheet = (Excel.Worksheet)Globals.ThisAddIn.Application.ActiveSheet;
        //Did not have to write all of this after all.
        //

        //private ExcelWrapper.Wrapper apiWrap = new ExcelWrapper.Wrapper();

        //Alex object is created in ThisAddin_startup, so that information about current active sheet and sheets is updated from document open
        //Non-static members are needed for remaining on the current worksheet
        
        private Excel.Worksheet _currentWorkSheet = null;
        private Excel.Workbook _currentWorkBook = null;
        private Excel.Application _currentApplication = null;
        private bool _isFirstTimeFlag = true;

        //private string _currentWorkSheetName = null;
        //private int _currentWorkSheetCount;
        //private List<string> _currentWorkSheetNames = null;

        public event Excel.WorkbookEvents_SheetActivateEventHandler SheetActivate;

        public TestCurrentSpreadSheet() {

            //Getting Excel's application object instance
            int iSection = 0, iTries = 0;
            tryAgain:
            try
            {
                iSection = 1; //Attempting GetActiveObject
                this.CurrentApplication = (Excel.Application)Marshal.GetActiveObject("Excel.Application");
                iSection = 0; //GetActiveObject succeeded so resume or go for normal error handling if needed
                this.CurrentApplication.Visible = true;
            }
            catch (Exception err)
            {
                System.Console.WriteLine("Visual C# .NET Error Attaching to Running Instance of Office Application .. yet.");
                if (iSection == 1)
                {
                    //GetObject may have failed because the
                    //Shell function is asynchronous; enough time has not elapsed
                    //for GetObject to find the running Office application. Wait
                    //1/2 seconds and retry the GetObject. If we try 20 times
                    //and GetObject still fails, we assume some other reason
                    //for GetObject failing and exit the procedure.
                    iTries++;
                    if (iTries < 20)
                    {
                        System.Threading.Thread.Sleep(500); // Wait 1/2 seconds.
                        goto tryAgain; //resume code at the GetObject line
                    }
                    else
                    {
                        MessageBox.Show("GetObject still failing.  Process ended.");
                    }

                }
                else
                {
                    //iSection == 0 so normal error handling
                    MessageBox.Show(err.Message);
                }
            }
        }


        // Application.SheetActivate and Workbook.SheetActivate events need to be handled for tracking currently active sheet
        // TODO write Application level and Workbook level event listeners for deactivated worksheets
        //Debug specific code/ not final
        public void createAllWorkSheetStats()
        {
            if (this._isFirstTimeFlag)
            {

                try
                {   
                    this.CurrentWorkBook = (Excel.Workbook)this.CurrentApplication.ActiveWorkbook;
                }
                catch (NullReferenceException)
                {
                    this.CurrentWorkBook = (Excel.Workbook)Globals.ThisAddIn.Application.ActiveWorkbook;
                }
                
                try
                {
                    this.CurrentWorkSheet = (Excel.Worksheet)this.CurrentWorkBook.ActiveSheet;
                }
                catch (NullReferenceException)
                {
                    this.CurrentWorkSheet = (Excel.Worksheet)Globals.ThisAddIn.Application.ActiveSheet;
                    //this.CurrentWorkSheet = (Excel.Worksheet)this.CurrentApplication.ActiveWorkbook.Sheets[1];
                }
                
                //this.CurrentWorkSheetCount = apiWrap.WorksheetCount;
                //this.CurrentWorkSheetName = apiWrap.CurrentWorksheet;
                //this.CurrentWorkSheetNames = apiWrap.WorksheetNames;
                MessageBox.Show(this.CurrentWorkSheet.ToString());
                System.Console.WriteLine("Enough is enough.");
            }
            else
            {
                updateWorkSheetStats();
            }
        }

        public void updateWorkSheetStats()
        {
            if (this._isFirstTimeFlag)
            {
                createAllWorkSheetStats();
            }
            else
            {
                this.CurrentWorkBook = (Excel.Workbook)this.CurrentApplication.ActiveWorkbook;
                this.CurrentWorkSheet = (Excel.Worksheet)this.CurrentWorkBook.ActiveSheet;
                //this.CurrentWorkSheetCount = apiWrap.WorksheetCount;
                //this.CurrentWorkSheetName = apiWrap.CurrentWorksheet;
                //this.CurrentWorkSheetNames = apiWrap.WorksheetNames;
                System.Console.WriteLine(this.CurrentWorkSheet.ToString());
            }
        }

        private void ThisWorkbook_SheetActivate(object Sh)
        {
            createAllWorkSheetStats();
            //Worksheet sheet = (Worksheet)Sh; 
            System.Windows.Forms.MessageBox.Show("WorksheetStats updated");
        }


        private void WorkbookSheetActivate()
        {
            this.SheetActivate += new Excel.WorkbookEvents_SheetActivateEventHandler(ThisWorkbook_SheetActivate);
        }


        //just setters and getters
        public Excel.Worksheet CurrentWorkSheet
        {
            get { return _currentWorkSheet; }
            set { _currentWorkSheet = value; }
        }


        public Excel.Workbook CurrentWorkBook
        {
            get { return _currentWorkBook; }
            set { _currentWorkBook = value; }
        }

        public Excel.Application CurrentApplication { get; set; }
        //Refactored + new codes are mostly up here >>>>>>>>>>>>>> END <<<<<<<<<<<<<<<<<<<<<<<



        //public string CurrentWorkSheetName
        //{
        //    get { return _currentWorkSheetName; }
        //    set { _currentWorkSheetName = value; }
        //}

        //public int CurrentWorkSheetCount
        //{
        //    get { return _currentWorkSheetCount; }
        //    set { _currentWorkSheetCount = value; }
        //}


        //public List<string> CurrentWorkSheetNames
        //{
        //    get { return _currentWorkSheetNames; }
        //    set { _currentWorkSheetNames = value; }
        //}


    }
}
