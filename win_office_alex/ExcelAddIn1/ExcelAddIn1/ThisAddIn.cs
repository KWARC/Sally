using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Xml.Linq;
using Excel = Microsoft.Office.Interop.Excel;
using Office = Microsoft.Office.Core;
using Microsoft.Office.Tools.Excel;
using sally;


namespace ExcelAddIn1
{
    //public delegate void CurrentSpreadSheetUpdateHandler(object sender, EventArgs e);

    public partial class ThisAddIn
    {
        /* Keep a reference to the button so that it doesn't get collected by the GC
         * */

        //no projectMode and saveMap anymore. Adapt and reuse this in case more options are added to Sally Right Click Menu
        //private Office.CommandBarPopup subMenu;
        //private Office.CommandBarButton projectMode;
        //private Office.CommandBarButton saveMap;

        private Excel.Range selectedCells;      //Reference to the selected range so that we can work with it
        // for the context menu
        private Office.CommandBar cellbar;
        private Office.CommandBarButton lookupButton; 
        
        //public event CurrentSpreadSheetUpdateHandler Updated;
        
        private void ThisAddIn_Startup(object sender, System.EventArgs e)
        {
            DefineShortcutMenu();
            Application.SheetBeforeRightClick += new Excel.AppEvents_SheetBeforeRightClickEventHandler(Application_SheetBeforeRightClick);
            //projectMode.Click += new Microsoft.Office.Core._CommandBarButtonEvents_ClickEventHandler(projectMode_Click);//projectMode is obsolete
            //saveMap.Click += new Microsoft.Office.Core._CommandBarButtonEvents_ClickEventHandler(saveMap_Click);
            lookupButton.Click += new Microsoft.Office.Core._CommandBarButtonEvents_ClickEventHandler(lookupButton_Click);
            Alex.OnUpdateState += new Alex.StateUpdateHandler(AlexUpdate_ChangeMenus);
            //Register the current workbook and worksheet

            //CurrentSpreadSheet css = CurrentSpreadSheet.Instance;    
            //css.updateCurrentSpreadSheet();

            //listen for any newly activated worksheet
            
            //listeners moved to Ribbon_Load

        }

        //Mechanism to send message to Alex.cs whether the addin is ready for displaying lookup or not
        //and receiving from Alex whether to display sally menu items or not
        //states: true false only. //change to enum if relevant
        public delegate void LookupEventHandler(object sender, ProgressEventArgs e);
        public event LookupEventHandler OnLookupClick;

        public class ProgressEventArgs : EventArgs
        {   
            public bool Click { get; private set; }

            public ProgressEventArgs(bool click)
            {
                Click = click;
            }
        }

        private void AllowLookup(bool clicked)
        {
            // Make sure someone is listening to event
            if (OnLookupClick == null) return;

            ProgressEventArgs args = new ProgressEventArgs(clicked);
            OnLookupClick(this, args);
        }

        private void AlexUpdate_ChangeMenus(object sender, Alex.StateEventArgs e)
        {
            if(e.State == Alex.AlexState.CONNECTED)
            {
                lookupButton.Visible = true;
                //subMenu.Visible = true;
            }
            else if ((e.State == Alex.AlexState.DISCONNECTED)) //|| (e.State == Alex.AlexState.EMPTY)
            {
                lookupButton.Visible = false;
                //subMenu.Visible = false;
            }
        }


        private void lookupButton_Click(Microsoft.Office.Core.CommandBarButton cmdBarbutton, ref bool cancel)
        {
            AllowLookup(true);
        }




        /// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>  START MARKER   <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
        /// <summary>
        /// This method is used to get the name of the current file. It is a duplicate of the method in Alex. Will be removed after code is refactored fully
        /// </summary>
        /// <exception cref="Exception">An exception is thrown if the document is not saved.</exception>
        /// <returns>Returns the URL representing the full name of the document</returns>
        public String getFileName()
        {
            CurrentSpreadSheet css = CurrentSpreadSheet.Instance;
            if (css.CurrentWorkBook.Name == null)
                throw new Exception("You must save the file before connecting to Sally\n");

            css.CurrentFilename = css.CurrentWorkBook.FullNameURLEncoded;
            System.Uri uri = new System.Uri(css.CurrentFilename);
            return uri.AbsoluteUri;
        }

        
        void saveMap_Click(Microsoft.Office.Core.CommandBarButton Ctrl, ref bool CancelDefault)
        {
            try
            {
                string filename = getFileName();
                Alex.sendMessage("/service/alex/saveMap", RequestASM.CreateBuilder().SetFilename(filename).Build());
            }
            catch (Exception ex)
            {
                System.Windows.Forms.MessageBox.Show(ex.Message);
            }
        }




        void writeToText_Click(Office.CommandBarButton Ctrl, ref bool CancelDefault)
        {
            try
            {
                System.DateTime currentDateTime = System.DateTime.Now;
                string dateStamp = currentDateTime.ToString("dMMMMyyyy_hh.mm.ss");

                string fileName = System.Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments) + "\\\\" + dateStamp + ".txt";
                System.IO.StreamWriter sw = new System.IO.StreamWriter(fileName);

                foreach (Excel.Range cell in selectedCells.Cells)
                {
                    if (cell.Value2 != null)
                    {
                        sw.WriteLine(cell.Value2.ToString());
                    }
                }
                sw.Close();
            }
            catch (Exception ex)
            {
                System.Windows.Forms.MessageBox.Show(ex.Message);
            }
        }

        /*
         * Gets the selected cells. It will be useful for context menu interaction with ranges
         */
        void Application_SheetBeforeRightClick(object Sh, Excel.Range Target, ref bool Cancel)
        {
            selectedCells = Target;
        }

        /*
         * Adds the buttons and the Sally sub menu to the context menu
         */
        private void DefineShortcutMenu()
        {

            Office.MsoControlType menuItem = Office.MsoControlType.msoControlButton;
            

            cellbar = Application.CommandBars["Cell"];

            lookupButton = (Office.CommandBarButton)cellbar.FindControl(menuItem, 0, "AlexRightClickMenu", missing, missing);
            if (lookupButton == null)
            {
                // first time so add the button
                lookupButton = (Office.CommandBarButton)cellbar.Controls.Add(menuItem, missing, missing, 1, true);
                lookupButton.Caption = "Sally Frame";
                lookupButton.BeginGroup = true;
                lookupButton.Tag = "1";
                lookupButton.Visible = false;
                
            }

            //Office.MsoControlType sub = Office.MsoControlType.msoControlPopup;
            //subMenu = (Office.CommandBarPopup)cellbar.Controls.Add(sub, missing, missing, 2, true);
            //subMenu.Caption = "Sally Options";
            //subMenu.Tag = "2";
            //subMenu.Visible = false;

            //projectMode = (Office.CommandBarButton)subMenu.Controls.Add(menuItem, missing, missing, 1, true);
            //projectMode.Style = Office.MsoButtonStyle.msoButtonCaption;
            //projectMode.Caption = "Project Mode";
            //projectMode.Tag = "1";

            //saveMap = (Office.CommandBarButton)subMenu.Controls.Add(menuItem, missing, missing, 2, true);
            //saveMap.Style = Office.MsoButtonStyle.msoButtonCaption;
            //saveMap.Caption = "Save semantic map";
            //saveMap.Tag = "2";

        }

        private void ThisAddIn_Shutdown(object sender, System.EventArgs e)
        {
        }
        #region VSTO generated code

        /// <summary>
        /// Required method for Designer support - do not modify
        /// the contents of this method with the code editor.
        /// </summary>
        private void InternalStartup()
        {
//            this.Application.WorkbookOpen += new Excel.AppEvents_WorkbookOpenEventHandler(Application_WorkbookOpen);
            this.Startup += new System.EventHandler(ThisAddIn_Startup);
            this.Shutdown += new System.EventHandler(ThisAddIn_Shutdown);
        }

        #endregion


        ///
        ///Semantic mode is now obsolete.
        // * Change the Semantic mode to 
        // * Lookup
        // */
        //void defLook_Click(Microsoft.Office.Core.CommandBarButton Ctrl, ref bool CancelDefault)
        //{
        //    try
        //    {
        //        string filename = getFileName();
        //        Alex.sendMessage("/service/alex/setSemanticMode", SemanticMode.CreateBuilder().SetMode(SemanticMode.Types.SemMode.DEFINITION_LOOKUP).SetFileName(filename).Build());
        //    }
        //    catch (Exception ex)
        //    {
        //        System.Windows.Forms.MessageBox.Show(ex.Message);
        //    }
        //}

        ///*
        //* Change the Semantic mode to Project Mode
        //*/
        //void projectMode_Click(Microsoft.Office.Core.CommandBarButton Ctrl, ref bool CancelDefault)
        //{
        //    try
        //    {
        //        string filename = getFileName();
        //        Alex.sendMessage("/service/alex/setSemanticMode", SemanticMode.CreateBuilder().SetMode(SemanticMode.Types.SemMode.PROJECT_MODE).SetFileName(filename).Build());
        //    }
        //    catch (Exception ex)
        //    {
        //        System.Windows.Forms.MessageBox.Show(ex.Message);
        //    }
        //}

        ///*
        // * Change the Semantic mode to semantic navigation
        // */
        //void semMode_Click(Microsoft.Office.Core.CommandBarButton Ctrl, ref bool CancelDefault)
        //{
        //    try
        //    {
        //        string filename = getFileName();
        //        Alex.sendMessage("/service/alex/setSemanticMode", SemanticMode.CreateBuilder().SetMode(SemanticMode.Types.SemMode.SEMANTIC_NAVIGATION).SetFileName(filename).Build());
        //    }
        //    catch (Exception ex)
        //    {
        //        System.Windows.Forms.MessageBox.Show(ex.Message);
        //    }

        //}

        ///// >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>  END MARKER   <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<

    }
}
