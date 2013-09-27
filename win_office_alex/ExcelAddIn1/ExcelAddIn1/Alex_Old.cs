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
using Microsoft.Office.Core;
using System.Reflection;
using System.Collections;
using System.Xml.Linq;
using ExcelWrapper;

namespace ExcelAddIn1
{
    public class Alex_Old //public partial class
    {
        static Worksheet _sheet = null; //current worksheet
        static Workbook _book = null;   //current workbook

        static Range _activeCell = null;
        static int _lineStyle;
        static int _borderWeight;
        static Process sallyProc;
        static bool doNotReact = false;
        static BayeuxClient client; //Needs to be static so that we can send messages. 
        static bool connected = false;
        static HashSet<Microsoft.Office.Interop.Excel.Workbook> activeDocuments = new HashSet<Workbook>();

        public static Workbook Book
        {
            get { return Alex_Old._book; }
            set { Alex_Old._book = value; }
        }

        public static Worksheet Sheet
        {
            get { return Alex_Old._sheet; }
            set { Alex_Old._sheet = value; }
        }

        private void Ribbon1_Load(object sender, RibbonUIEventArgs e)
        {

            Globals.ThisAddIn.Application.WorkbookOpen += new Microsoft.Office.Interop.Excel.AppEvents_WorkbookOpenEventHandler(Application_WorkbookOpen);
            Globals.ThisAddIn.Application.WorkbookActivate += new Microsoft.Office.Interop.Excel.AppEvents_WorkbookActivateEventHandler(Application_WorkbookActivate);
        }

        private void Application_WorkbookOpen(Workbook Wb)
        {
            Application_WorkbookActivate(Wb);
        }


        /// <summary>
        /// Check if the sheet is in the set of active sheets and modify the buttons accordingly.
        /// </summary>
        /// <param name="Wb"> The active workbook.</param>
        private void Application_WorkbookActivate(Microsoft.Office.Interop.Excel.Workbook Wb)
        {
            _book = Wb;
            _sheet = Wb.ActiveSheet;
            _sheet.SelectionChange += new DocEvents_SelectionChangeEventHandler(sheet_SelectionChange);
            _book.BeforeClose += new WorkbookEvents_BeforeCloseEventHandler(beforeClose);
            if (!activeDocuments.Contains(Wb))
            {
                button1.Enabled = true;
                button2.Enabled = false;
            }
            else
            {
                button1.Enabled = false;
                button2.Enabled = true;
            }
        }

        /// <summary>
        /// If this document is connected to Sally, remove it from the sets of active documents.
        /// If it is the last document connected to Sally, close the connection.
        /// </summary>
        /// <param name="Cancel"></param>
        private void beforeClose(ref bool Cancel)
        {

            if (activeDocuments.Contains(_book))
            {
                activeDocuments.Remove(_book);
            }

            if (activeDocuments.Count == 0 && client != null && client.Connected)
            {
                client.disconnect();
                connected = false;
            }
        }

        private static void removeBorder()
        {
            if (_activeCell != null)
            {
                // TODO: this is a hack, but it works for our test case
                // the borders should be saved and then restored
                foreach (Border b in _activeCell.Borders)
                {
                    b.LineStyle = XlLineStyle.xlLineStyleNone;
                }
            }
        }

        private static void addBorder()
        {
            _activeCell = Globals.ThisAddIn.Application.ActiveCell;
            _lineStyle = _activeCell.Borders.LineStyle;
            _borderWeight = _activeCell.Borders.Weight;
            _activeCell.Borders.Weight = Microsoft.Office.Interop.Excel.XlBorderWeight.xlThick;
        }



        private void sheet_SelectionChange(Range rng)
        {

            int startCol, startRow, endCol, endRow;
            string fileName;
            try
            {
                fileName = getFileName();
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
                    Display.CellTopLeftPixels(rng);
                    Microsoft.Office.Interop.Excel.Range range = Globals.ThisAddIn.Application.Selection as Microsoft.Office.Interop.Excel.Range;
                    string address = range.get_AddressLocal().ToString();
                    //Problem for big range
                    Util.convertRangeAddress(address, out startCol, out startRow, out endCol, out endRow);
                    RangeSelection sel = RangeSelection.CreateBuilder().SetStartCol(startCol).SetStartRow(startRow).SetEndRow(endRow).SetEndCol(endCol).Build();
                    ScreenCoordinates coords = ScreenCoordinates.CreateBuilder().SetX((int)Display.left).SetY((int)Display.top).Build();
                    sendMessage("/service/Alex_Old/selectRange", Alex_OldClick.CreateBuilder().SetRange(sel).SetPosition(coords).SetFileName(fileName).SetSheet(Globals.ThisAddIn.Application.ActiveSheet.Name).Build());
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
            catch (Exception ex)
            {
                MessageBox.Show(ex.Message);
            }
        }

        /// <summary>
        /// This method is used to get the name of the current file.
        /// </summary>
        /// <exception cref="Exception">An exception is thrown if the document is not saved.</exception>
        /// <returns>Returns the URL representing the full name of the document</returns>
        public static String getFileName()
        {
            if (_book.Name == null)
                throw new Exception("You must save the file before connecting to Sally\n");
            return _book.Name;
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
            activeDocuments.Add(_book);
            try
            {
                string semanticData = getSemanticData();
                string fileName = getFileName();
                if (connected)
                {
                    WhoAmI whoami = WhoAmI.CreateBuilder().SetClientType(WhoAmI.Types.ClientType.Alex_Old).SetDocumentType(WhoAmI.Types.DocType.Spreadsheet).SetEnvironmentType(WhoAmI.Types.EnvironmentType.Desktop).Build();
                    sendMessage("/service/Alex_Old/register", whoami);
                    sendMessage("/service/sissi/loadSemanticData", SemanticData.CreateBuilder().SetData(semanticData).SetFileName(fileName).Build());
                }
                else
                {
                    String url = "http://localhost:8080/sally/cometd";
                    //String url = "http://localhost:8080/cometd";
                    Dictionary<string, object> options = new Dictionary<string, object>();
                    List<Cometd.Client.Transport.ClientTransport> transport = new List<Cometd.Client.Transport.ClientTransport> { new LongPollingTransport(options) };
                    client = new BayeuxClient(url, transport);
                    client.getChannel("/**").addListener(new MessageLogger());
                    client.handshake();
                    client.getChannel("/**").addListener(new MessageParser());
                    //TODO
                    // Talk to Constantin about this.
                    client.waitFor(1500, new List<BayeuxClient.State>() { BayeuxClient.State.CONNECTED });
                    System.Threading.Thread.Sleep(5000);
                    SetFocusToExcel();
                    WhoAmI whoami = WhoAmI.CreateBuilder().SetClientType(WhoAmI.Types.ClientType.Alex_Old).SetDocumentType(WhoAmI.Types.DocType.Spreadsheet).SetEnvironmentType(WhoAmI.Types.EnvironmentType.Desktop).Build();
                    sendMessage("/service/Alex_Old/register", whoami);
                    sendMessage("/service/sissi/loadSemanticData", SemanticData.CreateBuilder().SetData(semanticData).SetFileName(fileName).Build());
                    connected = (client.waitFor(1000, new List<BayeuxClient.State>() { BayeuxClient.State.CONNECTED }) == BayeuxClient.State.CONNECTED);
                }
                if (connected)
                {
                    button1.Enabled = false;
                    button2.Enabled = true;
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("You must save the document before starting Sally\n" + ex.Message);
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
        /// <summary>
        /// Used to select multiple ranges. It is currently unused and needs maintenance.
        /// </summary>
        /// <param name="ranges">The list of ranges we eant to select.</param>
        /// <param name="aSheet">Name of the sheet where the cells are located.</param>
        private static void selectMultipleRanges(List<RangeSelection> ranges, String aSheet)
        {
            //Microsoft.Office.Interop.Excel.Range range = (Microsoft.Office.Interop.Excel.Range)Globals.ThisAddIn.Application.ActiveWorkbook.Sheets["Profits"].Cells("B26,B19,B13", Type.Missing);
            //range.Select();
            int size = ranges.Count;
            string toSelect = "";
            Microsoft.Office.Interop.Excel.Worksheet sheet = Globals.ThisAddIn.Application.ActiveWorkbook.Sheets[aSheet];
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
                if (msg.GetType().ToString().Equals("sally.CellPosition"))
                {
                    CellPosition pos = (CellPosition)msg;
                    int col = pos.Col;
                    int row = pos.Row;
                    int sheet = pos.Sheet;
                    RangeSelection click = RangeSelection.CreateBuilder().SetStartCol(col).SetStartRow(row).SetEndRow(row).SetEndCol(col).SetSheet(sheet + "").Build();
                    moveCursorAt(click);

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
        /// Move the cursor at the position specified by RangeSelection
        /// </summary>
        /// <param name="click">Position where to move the cursor.</param>
        public static void moveCursorAt(RangeSelection click)
        {
            //   Globals.ThisAddIn.Application.Workbooks[click.]
            Microsoft.Office.Interop.Excel.Range range = Globals.ThisAddIn.Application.ActiveSheet.Cells[click.StartRow + 1, click.StartCol + 1].Select();
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

            if (activeDocuments.Contains(_book))
            {
                activeDocuments.Remove(_book);
            }

            if (activeDocuments.Count == 0 && client != null && client.Connected)
            {
                client.disconnect();
                connected = false;
            }
            button1.Enabled = true;
            button2.Enabled = false;
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
        /// Get the semantic data from the spreadsheet
        /// </summary>
        /// <returns>JSON representing the semantic data.</returns>
        public string getSemanticData()
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
            Worksheet hidden = Globals.ThisAddIn.Application.ActiveWorkbook.Sheets["Hidden"];
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
