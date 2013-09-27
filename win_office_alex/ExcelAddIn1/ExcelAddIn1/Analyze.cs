using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using sally;
using Microsoft.Office.Interop.Excel;

namespace ExcelAddIn1
{
    class Analyze
    {
        /*
         * Returns the lineStyle of a border according to the Excel API
         */ 
        public static void lineStyle( Microsoft.Office.Interop.Excel.Border border, out int weight, out int style)
        {
            Microsoft.Office.Interop.Excel.XlLineStyle s = (XlLineStyle) border.LineStyle;
            Microsoft.Office.Interop.Excel.XlBorderWeight w = (XlBorderWeight) border.Weight;
            switch (s)
            {
                case XlLineStyle.xlLineStyleNone:
                    style = 0;
                    break;
                case XlLineStyle.xlContinuous:
                    style = 1;
                    break;
                case XlLineStyle.xlDash:
                    style = 2;
                    break;
                case XlLineStyle.xlDashDot:
                    style = 3;
                    break;
                case XlLineStyle.xlDashDotDot:
                    style = 4;
                    break;
                case XlLineStyle.xlDot:
                    style = 5;
                    break;
                case XlLineStyle.xlDouble:
                    style = 6;
                    break;
                case XlLineStyle.xlSlantDashDot:
                    style = 7;
                    break;
                default:
                    style =0;
                    break;
            }

            switch (w)
            {
                case XlBorderWeight.xlHairline:
                    weight = 0;
                    break;
                case XlBorderWeight.xlThin:
                    weight = 1;
                    break;
                case XlBorderWeight.xlMedium:
                    weight = 2;
                    break;
                case XlBorderWeight.xlThick:
                    weight = 3;
                    break;
                default:
                    weight = 0;
                    break;

            }
        }

        /*
         * Returns the cell Border of a cell
         */ 
        public static CellBorder getBorder(Range cell)
        {
            sally.BorderLine top, right, bottom, left;
            CellBorder ret = null;
            int weight, style;
            Microsoft.Office.Interop.Excel.Border aux;
            try
            {
                Microsoft.Office.Interop.Excel.Borders borders= cell.Borders;
                aux = borders[XlBordersIndex.xlEdgeTop];
                lineStyle(aux,out weight, out style);
                top = sally.BorderLine.CreateBuilder().SetBorderColor((int)aux.Color).SetFormatStyle(0).SetExcelBorderStyle(style).SetExcelBorderWeight(weight).Build();
               
                aux = borders[XlBordersIndex.xlEdgeRight];
                lineStyle(aux, out weight, out style);
                right = sally.BorderLine.CreateBuilder().SetBorderColor((int)aux.Color).SetFormatStyle(0).SetExcelBorderStyle(style).SetExcelBorderWeight(weight).Build();

                aux = borders[XlBordersIndex.xlEdgeLeft];
                lineStyle(aux, out weight, out style);
                left = sally.BorderLine.CreateBuilder().SetBorderColor((int)aux.Color).SetFormatStyle(0).SetExcelBorderStyle(style).SetExcelBorderWeight(weight).Build();

                aux = borders[XlBordersIndex.xlEdgeBottom];
                lineStyle(aux, out weight, out style);
                bottom = sally.BorderLine.CreateBuilder().SetBorderColor((int)aux.Color).SetFormatStyle(0).SetExcelBorderStyle(style).SetExcelBorderWeight(weight).Build();

                ret = CellBorder.CreateBuilder().SetBottom(bottom).SetLeft(left).SetRight(right).SetTop(top).Build();
            }
            catch (Exception ex) { }
            return ret;
        }

        /*
         * Returns the font of the contents of a cell
         */
        public static sally.Font getFont(Range cell)
        {
            String fontName = "";
            sally.Font ret = null;
            int fontColor = 0;
            float fontSize = 0;
            bool isUnderlined = false;
            fontName = cell.Font.Name;
            fontColor = (int) cell.Font.Color;
            fontSize = (float) cell.Font.Size;
            if ((XlUnderlineStyle) cell.Font.Underline != XlUnderlineStyle.xlUnderlineStyleNone)
                isUnderlined = true;
            ret = sally.Font.CreateBuilder().SetFontColor(fontColor).SetFontName(fontName).SetIsBold(cell.Font.Bold).SetIsItalic(cell.Font.Italic).SetIsUnderlined(isUnderlined).SetFontSize(fontSize).Build();
            return ret;
        }


        /*
         * Analyzez the cell for all its properties
         */ 
      /*  public static Cell analyzeCell(Worksheet sheet, Range cell, int row, int col)
        {
            Cell ret = null;
            sally.Font font = getFont(cell);
            CellBorder cellBorder = getBorder(cell);
            int backColor, cellMergedWidth, cellMergedHeight;
            int startRow, startCol, endRow, endCol;
            string value = "", formula = "";

            backColor = (int)cell.Interior.Color;
            Range mergedArea = cell.MergeArea;
            Util.convertRangeAddress(mergedArea.get_AddressLocal().ToString(), out startCol, out startRow, out endCol, out endRow);
            cellMergedHeight = endRow - startRow + 1;
            cellMergedWidth = endCol - startCol + 1;
            cell = mergedArea[1, 1];    //If the cell is merged we have to reference the first cell of the merged ones to get the information
            if (cell.HasFormula)
                formula = (string)cell.Formula;
            else
                value = (string)cell.Text;
 
            ret = Cell.CreateBuilder().SetBackColor(backColor).SetBorder(cellBorder).SetCellMergedHeight(cellMergedHeight).SetCellMergedWidth(cellMergedWidth).SetCol(col).SetRow(row).SetFont(font).SetFormula(formula).SetValue(value).Build();
            return ret;
        }
        */
        /*
         * Gets the data of a specified worksheet
         */ 
     /*   public static Sheet getSheetData(Worksheet sheet)
        {
            Sheet ret = null;
            int startRow, startCol, endRow, endCol;
            List<Cell> myList = new List<Cell>();
            try
            {
                Range usedRange = sheet.UsedRange;
                Util.convertRangeAddress(usedRange.get_AddressLocal().ToString(), out startCol, out startRow, out endCol, out endRow);
                startRow ++; 
                startCol ++;
                endRow ++;
                endCol ++;  //Adjust for Excel numbering of cells from 1
                for (int row = startRow; row <= endRow; row++)
                    for (int col = startCol; col <= endCol; col++)
                        myList.Add(analyzeCell(sheet, sheet.Cells[row,col], row, col));
                ret = Sheet.CreateBuilder().SetName(sheet.Name).AddRangeCells(myList).Build();
                
            }
            catch (Exception ex) { Console.WriteLine(ex); }
            return ret;
        }
        */

        /*
         * Analyzes a Excel workbook. Goes through the list of sheets and analyzez
         * each sheet using getSheetData
         */
    /*    public static Data analyzeDocument(Workbook workbook)
        {
            int numSheets = workbook.Sheets.Count;
            List<Sheet> myList = new List<Sheet>();
            Data ret = null;
            try{
            for (int sheetNum = 1; sheetNum <= numSheets; sheetNum++)
                myList.Add(getSheetData((Worksheet) workbook.Sheets[sheetNum]));
            ret = Data.CreateBuilder().AddRangeSheets(myList).Build();
            }
            catch (Exception ex) { Console.WriteLine(ex); }

            return ret;
        }
        */

    }
}
