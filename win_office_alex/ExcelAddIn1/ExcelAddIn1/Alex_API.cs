using System;
using System.Collections.Generic;
using System.Collections;
using System.Linq;
using System.Text;
using Excel = Microsoft.Office.Interop.Excel;
using ExcelTools = Microsoft.Office.Tools.Excel;
using Office = Microsoft.Office.Core;
using Marshal = System.Runtime.InteropServices.Marshal;

namespace ExcelAddIn1
{

    /// <summary>
    /// Specifies API calls that can be made to Alex.
    /// Uses COM Interop,  must have administrator or Power User security permissions 
    /// </summary>
    class Alex_API
    {

        private static bool successStatus = false;
        private static Excel.Application xlApp = Globals.ThisAddIn.Application;
        private static Excel.Workbook xlWorkbook = null;
        private static Excel.Sheets xlSheets = null;
        private static Excel.Worksheet xlSheet = null;


        /// <summary>
        /// Get values from a spreadsheet for the given range.
        /// </summary>
        /// <param name="filename"></param>
        /// <param name="sheetname"></param>
        /// <param name="toprow">Start row</param>
        /// <param name="lcolumn">Start col</param>
        /// <param name="height">Start height</param>
        /// <param name="width">Start width</param>
        /// <returns>List of strings</returns>
        public static System.Array getValuesFromRange(String filename, String sheetname, int startRow, int endRow, int startCol, int endCol)
        {
            System.Array rangeValues;
            try
            {
                successStatus = openXlApp();
                xlWorkbook = openXlWorkBook(filename);
                xlSheet = xlWorkbook.ActiveSheet;

                String xlRange = Util.rangeToExcelAddress(startRow, endRow, startCol, endCol);
                Excel.Range range = xlSheet.get_Range(xlRange);
                rangeValues = (System.Array)range.Cells.Value2;

                successStatus = quitXlApp();
            }
            finally
            {
                garbageCollect();
            }

            return rangeValues;
        }


        /// <summary>
        /// Set values to a spreadsheet for the given range.
        /// </summary>
        /// <param name="filename"></param>
        /// <param name="sheetname"></param>
        /// <param name="toprow">Start row</param>
        /// <param name="lcolumn">Start col</param>
        /// <param name="height">Start height</param>
        /// <param name="width">Start width</param>
        /// <returns>True if succeeded, false if failed.</returns>
        public static bool setValuesToRange(String filename, String sheetname, System.Array values, int startRow, int endRow, int startCol, int endCol)
        {
            try
            {
                successStatus = openXlApp();
                xlWorkbook = openXlWorkBook(filename);
                xlSheet = xlWorkbook.Sheets[sheetname];

                String xlRange = Util.rangeToExcelAddress(startRow, endRow, startCol, endCol);
                Excel.Range range = xlSheet.get_Range(xlRange);
                range.Value2 = values;


                successStatus = quitXlApp();
            }
            finally
            {
                garbageCollect();
            }

            return successStatus;
        }


        /// <summary>
        /// Creates a spreadsheet in the give xls filename. 
        /// </summary>
        /// <param name="filename">The complete filename with the absolute path.</param>
        /// <param name="sheetname">The name of the sheet e.g. Hidden</param>
        /// <returns>True if succeeded, false if failed.</returns>
        public static bool createWorksheet(String filename, String sheetname, bool needsToBeHidden = false)
        {
            successStatus = false;
            try
            {
                successStatus = openXlApp();
                CurrentSpreadSheet css = CurrentSpreadSheet.Instance;
                //checking if the call is being made for the currently open worbook. this is less expensive.
                if ((css.CurrentWorkBook != null) && (css.CurrentWorkBook.FullName == filename))
                {
                    xlSheets = css.CurrentWorkBook.Sheets as Excel.Sheets;
                }
                else
                {
                    xlWorkbook = openXlWorkBook(filename);
                    xlSheets = xlWorkbook.Sheets as Excel.Sheets;
                }

                xlSheet = (Excel.Worksheet)xlSheets.Add(xlSheets[xlSheets.Count + 1]);
                xlSheet.Name = sheetname;

                if (needsToBeHidden) xlSheet.Visible = Excel.XlSheetVisibility.xlSheetHidden;

                xlWorkbook.Save();
                successStatus = quitXlApp();
            }
            finally
            {
                garbageCollect();
            }

            return successStatus;
        }



        /// <summary>
        /// This opens an excel workbook.
        /// If the file is currently open, uses the cached COM object.
        /// Uses the following method:
        /// http://msdn.microsoft.com/en-us/library/ff194819.aspx
        /// </summary>
        /// <param name="filename">Full filename including path</param>
        /// <returns>An excel workbook</returns>
        private static Excel.Workbook openXlWorkBook(String filename)
        {   
            CurrentSpreadSheet css = CurrentSpreadSheet.Instance;
            //checking if the call if being made for the currently open worbook. this is less expensive.
            if ((css.CurrentWorkBook != null) && (css.CurrentWorkBook.FullName == filename))
            {
                xlWorkbook = css.CurrentWorkBook;
            }
            else
            {
                /// screw you too excel
                xlWorkbook = xlApp.Workbooks.Open(filename, 0, false, 5, "", "", false, Excel.XlPlatform.xlWindows, "",
                            true, false, 0, true, false, false);
            }
            return xlWorkbook;
        }



        private static bool openXlApp()
        {
            xlApp = new Excel.Application();

            if (xlApp == null)
            {
                return false;
            }

            return true;
        }

        private static bool quitXlApp()
        {
            xlWorkbook.Close(false);
            xlApp.Quit();
            return true;
        }


        private static void garbageCollect()
        {
            GC.Collect();
            GC.WaitForPendingFinalizers();
            Marshal.ReleaseComObject(xlSheet);
            Marshal.ReleaseComObject(xlSheets);
            Marshal.ReleaseComObject(xlWorkbook);
            Marshal.ReleaseComObject(xlApp);
            xlApp = null;
        }

    }
}
