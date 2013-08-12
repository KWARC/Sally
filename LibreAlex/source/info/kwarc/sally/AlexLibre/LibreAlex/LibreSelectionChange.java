package info.kwarc.sally.AlexLibre.LibreAlex;

import info.kwarc.sally.AlexLibre.Sally.SallyCommunication;
import info.kwarc.sally.AlexLibre.Sally.SallyUtils;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.AlexClick;
import sally.RangeSelection;
import sally.ScreenCoordinates;

import com.sun.star.awt.Point;
import com.sun.star.frame.XController;
import com.sun.star.lang.EventObject;
import com.sun.star.lib.uno.helper.WeakBase;
import com.sun.star.sheet.XCellRangeAddressable;
import com.sun.star.sheet.XSpreadsheetDocument;
import com.sun.star.table.CellAddress;
import com.sun.star.table.CellRangeAddress;
import com.sun.star.uno.UnoRuntime;

public final class LibreSelectionChange extends WeakBase
implements com.sun.star.view.XSelectionChangeListener
{
	Logger log;
	XSpreadsheetDocument xSpreadsheetDocument;

	// variable to hold the last known selection. Used for dismissing repeated events
	CellRangeAddress lastCellRangeAddress;
	SallyCommunication comm;
	
	public LibreSelectionChange( XSpreadsheetDocument xSpreadsheetDocument, SallyCommunication comm)
	{
		this.xSpreadsheetDocument = xSpreadsheetDocument;
		log = LoggerFactory.getLogger(this.getClass());
		lastCellRangeAddress = null;
		this.comm = comm;
	};

	@Override
	public void disposing(EventObject arg0) {

	}

	@Override
	public void selectionChanged(EventObject aEvent) {
		try {

			XController aCtrl = (XController) UnoRuntime.queryInterface(
					XController.class, aEvent.Source);
			if (aCtrl != null) { 
				XCellRangeAddressable xSheetCellAddressable = (XCellRangeAddressable) UnoRuntime
						.queryInterface(XCellRangeAddressable.class,
								aCtrl.getModel().getCurrentSelection());
				CellRangeAddress addr = xSheetCellAddressable.getRangeAddress();

				if (lastCellRangeAddress != null && SallyUtils.EqualCellRanges(addr, lastCellRangeAddress)) {
					return;
				}
				lastCellRangeAddress = addr;

				log.info(
						addr.StartColumn + ":" + addr.EndColumn + " "
								+ addr.StartRow + ":" + addr.EndRow);

				Point p = SallyUtils.getCellRangePosition(aCtrl.getFrame(), new CellAddress(addr.Sheet, addr.EndColumn + 1, addr.EndRow));

				String []spreadsheetNames = xSpreadsheetDocument.getSheets().getElementNames();

				RangeSelection range = RangeSelection.newBuilder().setSheet(spreadsheetNames[addr.Sheet])
						.setStartCol(addr.StartColumn).setEndCol(addr.EndColumn).setStartRow(addr.StartRow).setEndRow(addr.EndRow).build();

				String fName = SallyUtils.getDocumentName(xSpreadsheetDocument);
				AlexClick clickEvent = AlexClick.newBuilder().setFileName(fName).setSheet(spreadsheetNames[addr.Sheet]).setPosition(ScreenCoordinates.newBuilder().setX(p.X).setY(p.Y).build())
				.setRange(range).build();
				comm.sendMessage("/service/alex/click", clickEvent);
			}
		} catch (Exception e) {
			e.printStackTrace();
			log.error(e.getMessage());
		}
	}

}
