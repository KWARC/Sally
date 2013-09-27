using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Office.Tools.Ribbon;
using System.Windows.Forms;
using System.Net.Sockets;
using System.Runtime.InteropServices;
using Microsoft.Office.Interop.Excel;
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
using System.ComponentModel;

//using ExcelWrapper;

namespace ExcelAddIn1
{
    public partial class Alex //public partial class
    {
        private CurrentSpreadSheet css = CurrentSpreadSheet.Instance;


        static int _lineStyle;
        static int _borderWeight;
        static Process sallyProc;
        static bool doNotReact = false;
        static BayeuxClient client; //Needs to be static so that we can send messages. 
        static bool connected = false;
        static HashSet<Microsoft.Office.Interop.Excel.Workbook> activeDocuments = new HashSet<Workbook>();


        private void Ribbon1_Load(object sender, RibbonUIEventArgs e)
        {
            Globals.ThisAddIn.Application.WorkbookOpen += new Microsoft.Office.Interop.Excel.AppEvents_WorkbookOpenEventHandler(Application_WorkbookOpen);
            Globals.ThisAddIn.Application.WorkbookActivate += new Microsoft.Office.Interop.Excel.AppEvents_WorkbookActivateEventHandler(Application_WorkbookActivate);
            Globals.ThisAddIn.Application.SheetActivate += new Microsoft.Office.Interop.Excel.AppEvents_SheetActivateEventHandler(Application_WorkSheetActivateOrChange);
            Globals.ThisAddIn.OnLookupClick += new ThisAddIn.LookupEventHandler(Alex_AllowLookup);
        }


        void Application_WorkSheetActivateOrChange(object sh)
        {
            css.updateCurrentSpreadSheet();
            initOrResetCurrentSheetListeners();
        }


        private void Application_WorkbookOpen(Workbook Wb)
        {
            Application_WorkbookActivate(Wb);
        }

        ///note to self: hook up sheetchange with workbook activate actions. make a new method for this. worbookactivate itself should become brief

        /// <summary>
        /// Check if the sheet is in the set of active sheets and modify the buttons accordingly.
        /// </summary>
        /// <param name="Wb"> The active workbook.</param>
        private void Application_WorkbookActivate(Microsoft.Office.Interop.Excel.Workbook Wb)
        {
            css.updateCurrentSpreadSheet(Wb);
            initOrResetCurrentSheetListeners();
        }


        private void initOrResetCurrentSheetListeners()
        {
            //TODO throw events to Alex
            Worksheet cssCurrentWorkSheet = Globals.ThisAddIn.Application.ActiveSheet;
            cssCurrentWorkSheet.SelectionChange += new DocEvents_SelectionChangeEventHandler(sheet_SelectionChange);
            css.CurrentWorkBook.BeforeClose += new WorkbookEvents_BeforeCloseEventHandler(beforeClose);


            if ((activeDocuments == null) || (!isCurrentSheetEmpty())) //|| (!activeDocuments.Contains(currentSpreadSheet.CurrentWorkBook))
            {

                button1.Enabled = true;

                button2.Enabled = false;
            }
            else
            {
                button1.Enabled = false;
                button2.Enabled = true;
                UpdateState(AlexState.EMPTY);
            }
        }






        /// <summary>
        /// If this document is connected to Sally, remove it from the sets of active documents.
        /// If it is the last document connected to Sally, close the connection.
        /// </summary>
        /// <param name="Cancel"></param>
        private void beforeClose(ref bool Cancel)
        {

            if (activeDocuments.Contains(css.CurrentWorkBook))
            {
                activeDocuments.Remove(css.CurrentWorkBook);
            }

            if (activeDocuments.Count == 0 && client != null && client.Connected)
            {
                client.disconnect();
                connected = false;
            }
        }

        private void removeBorder()
        {
            if (css.CurrentRange != null)
            {
                // TODO: this is a hack, but it works for our test case
                // the borders should be saved and then restored
                foreach (Border b in css.CurrentRange.Borders)
                {
                    b.LineStyle = XlLineStyle.xlLineStyleNone;
                }
            }
        }

        private void addBorder()
        {
            css.CurrentRange = Globals.ThisAddIn.Application.ActiveCell; //
            _lineStyle = css.CurrentRange.Borders.LineStyle;
            _borderWeight = css.CurrentRange.Borders.Weight;
            css.CurrentRange.Borders.Weight = Microsoft.Office.Interop.Excel.XlBorderWeight.xlThick;
        }


        private void sheet_SelectionChange(Range rng)
        {
            css.CurrentRange = rng;
            Globals.ThisAddIn.Application.StatusBar = rng.ToString();
            sendCurrentRange();
        }

        private void sendCurrentRange()
        {
            int startCol, startRow, endCol, endRow;
            string fileName = "";
            try
            {
                fileName = getFileName();
            }
            catch (Exception ex)
            {
                MessageBox.Show("Here: " + ex.Message);
            }

            if (client != null && connected)
            {
                //    removeBorder();
                //   addBorder();

                if (doNotReact == true)
                {
                    doNotReact = false;
                    return;
                }
                // get the A1Format address using Globals.ThisAddIn.Application.ActiveCell.Address
                // get the coordinates using CellTopLeftPixels(Globals.ThisAddIn.Application.ActiveCell)               
                Display.CellTopLeftPixels(css.CurrentRange);
                Microsoft.Office.Interop.Excel.Range range = Globals.ThisAddIn.Application.Selection as Microsoft.Office.Interop.Excel.Range;
                string address = range.get_AddressLocal().ToString();
                //Problem for big range
                Util.convertRangeAddress(address, out startCol, out startRow, out endCol, out endRow);
                RangeSelection sel = RangeSelection.CreateBuilder().SetStartCol(startCol).SetStartRow(startRow).SetEndRow(endRow).SetEndCol(endCol).Build();
                ScreenCoordinates coords = ScreenCoordinates.CreateBuilder().SetX((int)Display.left).SetY((int)Display.top).Build();
                sendMessage("/service/alex/click", AlexClick.CreateBuilder().SetRange(sel).SetPosition(coords).SetFileName(fileName).SetSheet(css.CurrentWorkSheet.Name).Build()); //.SetSheet(Globals.ThisAddIn.Application.ActiveSheet.Name) ///service/alex/selectRange            
                Globals.ThisAddIn.Application.StatusBar = sel.ToString() + "," + coords.ToString() + "," + fileName + "," + css.CurrentWorkSheet.Name;
                //    Microsoft.Office.Interop.Excel.Worksheet activeSheet = Globals.ThisAddIn.Application.ActiveSheet;
                ///    var rang = activeSheet.get_Range("A1", "A1");
                //   rang.Select();
            }
            else
            {

                //MessageBox.Show(Globals.ThisAddIn.Application.ActiveCell.Address);
                //do nothing?
            }


        }

        /// <summary>
        /// TODO cache the filename too in the css object + update changes with events. There are too many calls to this function.
        /// </summary>
        public void requestSallyFrame()
        {
            string fileName = "";
            try
            {
                fileName = getFileName();
            }
            catch (Exception ex)
            {
                MessageBox.Show("Here: " + ex.Message);
            }
            sendMessage("/service/alex/sallyFrame", SallyFrame.CreateBuilder().SetFileName(fileName).Build());
        }


        /// <summary>
        /// This method is used to get the name of the current file.
        /// </summary>
        /// <exception cref="Exception">An exception is thrown if the document is not saved.</exception>
        /// <returns>Returns the URL representing the full name of the document</returns>
        public String getFileName()
        {
            if (css.CurrentWorkBook.Name == null)
                throw new Exception("You must save the file before connecting to Sally\n");
            css.CurrentFilename = css.CurrentWorkBook.FullNameURLEncoded;
            System.Uri uri = new System.Uri(css.CurrentFilename);
            return uri.AbsoluteUri;
        }

        /// <summary>
        /// Start Sally
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void button1_Click(object sender, RibbonControlEventArgs e)
        {
            /*  
             *     We don't really have settings for Java and Jar in this case.
             *     if (!File.Exists(Properties.Settings.Default.Java) || !File.Exists(Properties.Settings.Default.Jar))
                   return;
             */
            activeDocuments.Add(css.CurrentWorkBook);
            //CurrentSpreadSheet.CurrentWorkBooks.Add(currentSpreadSheet.CurrentWorkBook);

            string semanticData = getSemanticData(); //add/remove string "old" from the parameter to use old/not use old format

            try
            {

                string fileName = getFileName();
                if (connected)
                {
                    WhoAmI whoami = WhoAmI.CreateBuilder().SetClientType(WhoAmI.Types.ClientType.Alex).SetDocumentType(WhoAmI.Types.DocType.Spreadsheet).SetEnvironmentType(WhoAmI.Types.EnvironmentType.Desktop).Build();
                    sendMessage("/service/alex/register", whoami);
                    sendMessage("/service/alex/semanticData", AlexData.CreateBuilder().SetData(semanticData).SetFileName(fileName).Build());
                }
                else
                {
                    String url = "http://localhost:8181/cometd";
                    //String url = "http://localhost:8181/cometd";
                    Dictionary<string, object> options = new Dictionary<string, object>();
                    List<Cometd.Client.Transport.ClientTransport> transport = new List<Cometd.Client.Transport.ClientTransport> { new LongPollingTransport(options) };
                    client = new BayeuxClient(url, transport);
                    client.getChannel("/**").addListener(new MessageLogger());
                    client.handshake();
                    client.getChannel("/service/**").addListener(new MessageParser());
                    client.getChannel("/do/**").addListener(new MessageParser());
                    client.getChannel("/get/**").addListener(new MessageParser());

                    //TODO
                    // Talk to Constantin about this.
                    client.waitFor(1500, new List<BayeuxClient.State>() { BayeuxClient.State.CONNECTED });
                    System.Threading.Thread.Sleep(5000);
                    SetFocusToExcel();
                    WhoAmI whoami = WhoAmI.CreateBuilder().SetClientType(WhoAmI.Types.ClientType.Alex).SetDocumentType(WhoAmI.Types.DocType.Spreadsheet).SetEnvironmentType(WhoAmI.Types.EnvironmentType.Desktop).Build();
                    sendMessage("/service/alex/register", whoami);
                    sendMessage("/service/alex/semanticdata", AlexData.CreateBuilder().SetData(semanticData).SetFileName(fileName).Build()); /// /service/sissi/loadSemanticData
                    connected = (client.waitFor(1000, new List<BayeuxClient.State>() { BayeuxClient.State.CONNECTED }) == BayeuxClient.State.CONNECTED);
                }
                if (connected)
                {
                    //Enable stop button and context menu items. disable start button.
                    button1.Enabled = false;
                    button2.Enabled = true;
                    UpdateState(AlexState.CONNECTED);
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("Please save the document to use Sally.\n");
                Globals.ThisAddIn.Application.StatusBar = "Details for Alex's dev: " + ex.Message;
                
            }

        }




        public static int sendMessage(String channel, Google.ProtocolBuffers.IMessage msg)
        {
            /**
             * Only send the message if the client has been initialized and is connected to the host.
             */
            if (client != null && client.Connected)
            {
                client.getChannel(channel).publish(Util.prepareMessage(msg));
            }
            return 0;
        }


        ////////////////////////////////////////////////////////////////////////////////////////////////
        //Mechanisms to update the context menu buttons and the ribbon ui
        //states: STARTED, CONNECTED, DISCONNECTED, EMPTY. Add more if needed //
        public delegate void StateUpdateHandler(object sender, StateEventArgs e);
        public static event StateUpdateHandler OnUpdateState;
        public enum AlexState
        {
            [Description("Alex connected, currentsheet not empty.")]
            CONNECTED,
            [Description("Alex disconnected, currentsheet not empty.")]
            DISCONNECTED,
            [Description("Currentsheet empty or not saved.")]
            EMPTY
        };

        public class StateEventArgs : EventArgs
        {   //change to enum 
            public AlexState State { get; private set; }

            public StateEventArgs(AlexState state)
            {
                State = state;
            }
        }

        /// <summary>
        /// Update the state of the current Alex so as to change the Alex menu items accordingly.
        /// </summary>
        /// <param name="state"></param>
        private void UpdateState(AlexState state)
        {
            // Make sure someone is listening to event
            if (OnUpdateState == null) return;

            StateEventArgs args = new StateEventArgs(state);
            OnUpdateState(this, args);
        }

        /// <summary>
        /// Quick lookup of the current sheet to see if it is empty.
        /// Does not lookup all the sheets in the workbook as it may slow down many operations depending on this.
        /// </summary>
        /// <returns>true if empty, false if not</returns>
        private bool isCurrentSheetEmpty()
        {
            return (Globals.ThisAddIn.Application.WorksheetFunction.CountA(css.CurrentWorkSheet.Cells) == 0);
        }

        /// <summary>
        /// Receives the go ahead for displaying the sally lookup of the currently selected range.
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void Alex_AllowLookup(object sender, ThisAddIn.ProgressEventArgs e)
        {
            if (e.Click == true)
            {
                //MessageBox.Show("Click went through. Now attempting the lookup...");
                //lookup_CurrentRange();
                requestSallyFrame();
            }

        }


        ////////////////////////////////////////////////////////////////////////////////////////////////



        /// <summary>
        /// Used to select multiple ranges. It is currently unused and needs maintenance.
        /// </summary>
        /// <param name="ranges">The list of ranges we eant to select.</param>
        /// <param name="aSheet">Name of the sheet where the cells are located.</param>
        private void selectMultipleRanges(List<RangeSelection> ranges, String aSheet)
        {
            //Microsoft.Office.Interop.Excel.Range range = (Microsoft.Office.Interop.Excel.Range)Globals.ThisAddIn.Application.ActiveWorkbook.Sheets["Profits"].Cells("B26,B19,B13", Type.Missing);
            //range.Select();
            int size = ranges.Count;
            string toSelect = "";
            Microsoft.Office.Interop.Excel.Worksheet sheet = css.CurrentWorkSheet; //Globals.ThisAddIn.Application.ActiveWorkbook.Sheets[aSheet]
            sheet.Activate();

            for (int i = 0; i < size; i++)
            {
                toSelect = toSelect + Util.rangeToExcelAddress(ranges[i].StartRow, ranges[i].EndRow, ranges[i].StartCol, ranges[i].EndCol) + ";";
            }

            toSelect = toSelect + Util.rangeToExcelAddress(ranges[size - 1].StartRow, ranges[size - 1].EndRow, ranges[size - 1].StartCol, ranges[size - 1].EndCol);

            sheet.Range[toSelect, System.Reflection.Missing.Value].Select();
            //bla.Range["A5:A6;E4:F6", System.Reflection.Missing.Value].Select();
            //  Microsoft.Office.Interop.Excel.Range r1 = ( Microsoft.Office.Interop.Excel.Range) bla.get_Range("A1:A10", Missing.Value);
            //Microsoft.Office.Interop.Excel.Range r2 = (Microsoft.Office.Interop.Excel.Range)bla.get_Range("D1:D10", Missing.Value);


        }

        /// <summary>
        /// This class is used to log the messages sent and received using cometd.
        /// </summary>
        public class MessageLogger : IMessageListener
        {
            public MessageLogger() { }

            public void onMessage(IClientSession session, String channel, Cometd.Bayeux.IMessage message)
            {
                if (message.Successful)
                {
                    Console.WriteLine("had something on " + message.Channel);
                    Console.WriteLine("namely " + message.JSON);
                }

                if (channel.Equals("/do/select")) //|| (message is AlexRangeRequest)
                {

                }

                if (channel.Equals("/get/data"))
                {
                    //call Alex_API from here
                }

            }

            public void onMessage(IClientSessionChannel session, Cometd.Bayeux.IMessage message)
            {
                if (message.Successful)
                {
                    Console.WriteLine("had something on " + message.Channel);
                    Console.WriteLine("namely " + message.JSON);
                }
            }
        }
        /// <summary>
        /// This class is used to parse and react to incoming messages.
        /// </summary>
        public class MessageParser : IMessageListener
        {

            public void onMessage(IClientSessionChannel session, Cometd.Bayeux.IMessage message)
            {

                Console.WriteLine(message);
                Google.ProtocolBuffers.IMessage msg = Util.restoreMessage(message);
                if (msg.GetType().ToString().Equals("sally.AlexRangeRequest"))
                {
                    sally.AlexRangeRequest pos = (sally.AlexRangeRequest)msg;
                    String dump = pos.ToJson();
                   
                    string filename = new System.Uri(pos.FileName).AbsolutePath;
                    foreach (RangeSelection i in pos.SelectionList)
                    {
                        moveSelectionTo(i, filename);
                    }

                    //int col = pos.SelectionList;
                    //int row = pos.Row;
                    //int sheet = pos.Sheet;
                    //RangeSelection click = RangeSelection.CreateBuilder().SetStartCol(col).SetStartRow(row).SetEndRow(row).SetEndCol(col).SetSheet(sheet + "").Build();
                    //Microsoft.Office.Interop.Excel.Range range = Globals.ThisAddIn.Application.ActiveSheet.Cells[click.StartRow + 1, click.StartCol + 1].Select();

                }
                if (msg.GetType().ToString().Equals("sally.SaveASM"))
                {
                    SaveASM asm = (SaveASM)msg;
                    saveSemanticMap(asm.SemanticData);

                }
                /*    if (msg.GetType().ToString().Equals("sally.HighlightRanges"))
                    {
                        // Change to an Array or ArrayList. Might be faster.
                        List<HighlightRange> arr = new List<HighlightRange>(((HighlightRanges)msg).RangeList);
                    
                        String activeSheet = Globals.ThisAddIn.Application.ActiveSheet.Name;    // Get the name of the active sheet
                        int i=0;
                        foreach (HighlightRange el in arr)
                        {
                            if(el.Sheet.Equals(activeSheet, StringComparison.InvariantCultureIgnoreCase)){
                                selectMultipleRanges(new List<RangeSelection> (el.RangesList), el.Sheet);
                            //Highlight range
                                break;
                            }
                            i++;
                        }
                        if(i>=arr.Count && arr.Count >0){
                            selectMultipleRanges(new List<RangeSelection>(arr[0].RangesList), arr[0].Sheet);
                        }


                        int col = ((NavigateTo)msg).Col;
                        int row = ((NavigateTo)msg).Row;
                        String sheet = ((NavigateTo)msg).Sheet;
                        RangeSelection click = RangeSelection.CreateBuilder().SetStartCol(col).SetStartRow(row).SetEndRow(row).SetEndCol(col).SetSheet(sheet).Build();
                        moveCursorAt(click);

                    }*/
            }
        }


        /// <summary>
        /// Move the selection at the position specified by RangeSelection and filename
        /// Still depends on TheoFx to set the window to the foreground.
        /// </summary>
        /// <param name="click">Position where to move the cursor.</param>
        public static void moveSelectionTo(RangeSelection click, String filename)
        {
            //   Globals.ThisAddIn.Application.Workbooks[click.]
            string sheet = click.Sheet;
            Microsoft.Office.Interop.Excel.Workbook wb = Globals.ThisAddIn.Application.Workbooks[filename.Substring(filename.LastIndexOf("/") + 1)];
            Microsoft.Office.Interop.Excel.Worksheet ws = wb.Sheets[sheet];
            ws.Select();
            Microsoft.Office.Interop.Excel.Range range = wb.Sheets[sheet].Cells[click.StartRow + 1, click.StartCol + 1]; // Globals.ThisAddIn.Application.ActiveSheet.Cells[click.StartRow + 1, click.StartCol + 1].Select();
            range.Select();
            range.Activate();

        }

        /// <summary>
        /// Stop Sally
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void button2_Click(object sender, RibbonControlEventArgs e)
        {
            //MessageBox.Show(Globals.ThisAddIn.Application.ActiveCell.Count.ToString() + " " + Globals.ThisAddIn.Application.ActiveCell.MergeCells);
            /*
            try
            {
                if (!sallyProc.HasExited || !sallyProc.Responding)
                    sallyProc.Kill();
            }
            catch (Exception ex)
            {
                MessageBox.Show("Something went wrong... " + ex);
            }*/

            if (activeDocuments.Contains(css.CurrentWorkBook))
            {
                activeDocuments.Remove(css.CurrentWorkBook);
            }

            if (activeDocuments.Count == 0 && client != null && client.Connected)
            {
                client.disconnect();
                connected = false;
            }
            button1.Enabled = true;
            button2.Enabled = false;
            UpdateState(AlexState.DISCONNECTED);
        }

        /// <summary>
        /// Configure Sally
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void button3_Click(object sender, RibbonControlEventArgs e)
        {
            SettingsDialog frm1 = new SettingsDialog();
            frm1.ShowDialog();
        }

        /// <summary>
        /// Get the semantic data from the spreadsheet. There's an end-line after each cell's data.
        /// </summary>
        /// <returns>JSON representing the semantic data.</returns>
        /// 
        public string getSemanticData()
        {
            //Worksheet xlWs = css.CurrentWorkBook.Sheets["sally"];
            string dataPart = "";
            string concatValue = "";
            Worksheet interactionMap = Globals.ThisAddIn.Application.ActiveWorkbook.Sheets["sally"];
            double usedRows = Globals.ThisAddIn.Application.WorksheetFunction.CountA(interactionMap.Columns[1]);
            int numRows = (int)usedRows;
            Range range = interactionMap.get_Range(Util.str_int_ToExcelAddress("A", 1, numRows));
            if (range != null)
            {
                foreach (Range r in range)
                {
                    dataPart = r.Value;
                    //dataPart.TrimEnd('\r','\n','\t');
                    concatValue += dataPart;
                }
            }

            if (concatValue == "")
                throw new Exception("Create \"sally\" sheet and put the semantic data at position A1");
            else
                return concatValue;
        }


        /// <summary>
        /// Get the semantic data from the spreadsheet_ Old version for compatibility/demos/tests
        /// </summary>
        /// <returns>JSON representing the semantic data.</returns>
        public string getSemanticData(string old)
        {
            string data = Globals.ThisAddIn.Application.ActiveWorkbook.Sheets["Hidden"].Range("A1").Value;
            if (data == null)
                throw new Exception("Create \"Hidden\" sheet and put the semantic data at position A1");
            else
                return data;

        }


        /// <summary>
        /// Saves semantic data received from Sally in cell B2 of sheet Hidden.
        /// </summary>
        /// <param name="data"></param>
        public static void saveSemanticMap(string data)
        {
            Worksheet hidden = Globals.ThisAddIn.Application.ActiveWorkbook.Sheets["sally"];
            if (hidden != null)
                hidden.Range["B2"].Value = data;
            else
                MessageBox.Show("In order to save the semantic map, you must create a sheet called \"Hidden\"");
        }


        public void SetFocusToExcel()
        {
            IntPtr h = APIUtils.GetXLMainWindowHandle(APIUtils.GetDesktopWindow());
            APIUtils.SetFocus(h);
        }



        public class APIUtils
        {
            public static IntPtr GetXLMainWindowHandle(IntPtr DesktopHandle)
            {
                return FindMainWindowInProcess(DesktopHandle, String.Empty, "XLMAIN");
            }

            internal static IntPtr FindMainWindowInProcess(IntPtr HWNDParent, string WindowName, string WindowClass)
            {
                IntPtr FoundWindow = IntPtr.Zero;

                string FindClass = String.Empty;
                string FindName = String.Empty;
                uint WindowProcessID;

                IntPtr tempWindow = GetWindow(HWNDParent, GW_CHILD);
                while ((int)tempWindow > 0)
                {
                    FindName = GetWindowText(tempWindow);
                    FindClass = GetClassName(tempWindow);

                    bool CompareClass = ((FindClass.IndexOf(WindowClass) >= 0) || (WindowClass == String.Empty));
                    bool CompareCaption = ((FindName.IndexOf(WindowName) >= 0) || (WindowName == String.Empty));

                    if (CompareClass && CompareCaption)
                    {
                        GetWindowThreadProcessId(tempWindow, out WindowProcessID);
                        if (GetCurrentProcessId() == WindowProcessID)
                        {
                            FoundWindow = tempWindow;
                            if (IsWindowVisible(FoundWindow))
                            {
                                break;
                            }
                        }
                    }
                    tempWindow = GetWindow(tempWindow, GW_HWNDNEXT);
                }
                return FoundWindow;
            }

            [DllImport("user32.dll")]
            public static extern IntPtr SetFocus(IntPtr hWnd);

            [DllImport("user32.dll")]
            public static extern IntPtr GetDesktopWindow();

            [DllImport("User32.dll", CharSet = CharSet.Auto)]
            public static extern IntPtr GetWindow(IntPtr hwnd, int uCmd);

            [DllImport("user32.dll")]
            public static extern int GetWindowText(IntPtr hwnd,
                [In][Out]StringBuilder lpClassName, int nMaxCount);

            [DllImport("user32.dll")]
            public static extern int GetClassName(IntPtr hwnd,
                [In][Out]StringBuilder lpClassName, int nMaxCount);

            [DllImport("user32.dll")]
            public static extern bool IsWindowVisible(IntPtr hWnd);

            [DllImport("user32.dll", SetLastError = true)]
            public static extern uint GetWindowThreadProcessId(IntPtr hWnd, out uint lpdwProcessId);

            [DllImport("kernel32.dll")]
            public static extern uint GetCurrentProcessId();

            public static string GetWindowText(IntPtr handle)
            {
                System.Text.StringBuilder lpBuffer = new System.Text.StringBuilder(255);
                if (GetWindowText(handle, lpBuffer, 255) > 0)
                {
                    return lpBuffer.ToString();
                }
                else
                    return "";
            }

            public static string GetClassName(IntPtr handle)
            {
                System.Text.StringBuilder className = new System.Text.StringBuilder(255);
                if (GetClassName(handle, className, 255) > 0)
                {
                    return className.ToString();
                }
                else
                    return "";
            }

            public const int GW_CHILD = 5;
            public const int GW_HWNDNEXT = 2;

        }
    }

}
