package info.kwarc.sally.AlexLibre.Sally;

import com.sun.star.accessibility.XAccessible;
import com.sun.star.accessibility.XAccessibleComponent;
import com.sun.star.accessibility.XAccessibleContext;
import com.sun.star.accessibility.XAccessibleTable;
import com.sun.star.awt.Point;
import com.sun.star.awt.XWindow;
import com.sun.star.frame.XDesktop;
import com.sun.star.frame.XFrame;
import com.sun.star.frame.XStorable;
import com.sun.star.sheet.XSpreadsheetDocument;
import com.sun.star.table.CellAddress;
import com.sun.star.table.CellRangeAddress;
import com.sun.star.uno.UnoRuntime;
import com.sun.star.uno.XComponentContext;

public class SallyUtils {
	static public XDesktop getDesktop(XComponentContext m_xContext) throws Exception {
		XDesktop xDesktop;
		Object desktop = m_xContext.getServiceManager()
				.createInstanceWithContext(
						"com.sun.star.frame.Desktop", m_xContext);

		xDesktop = (XDesktop) UnoRuntime.queryInterface(
				XDesktop.class, desktop);
		return xDesktop;
	}

	static public String getDocumentName(XSpreadsheetDocument xSpreadsheetDocument) {
		XStorable xStorable = (XStorable) UnoRuntime.queryInterface(
				XStorable.class, xSpreadsheetDocument);

		if (xStorable == null)
			return null;
		return xStorable.getLocation();
	}

	static public boolean EqualCellRanges(CellRangeAddress a1, CellRangeAddress a2) {
		return a1.Sheet == a2.Sheet && a1.StartColumn == a2.StartColumn && a1.EndColumn == a2.EndColumn && a1.StartRow == a2.StartRow && a1.EndRow == a2.EndRow;
	}

	/**
	 * traverses the accessibility tree and returns the first
	 * {@link XAccessibleContext} with the given role
	 * 
	 * @param accessibleContext
	 *            the context to start searching with
	 * @param role
	 *            the role of the context that should be returned
	 * @return the first XAccessibleContext found with the given role or
	 *         <code>null</code>
	 * */
	static private XAccessibleContext getAccessibleForRole(
			XAccessibleContext accessibleContext, short role) {
		XAccessibleContext ret = null;
		XAccessibleContext accessibleContext2 = null;
		int count = accessibleContext.getAccessibleChildCount();
		for (int i = 0; i < count; i++) {
			if (ret != null)
				return ret;
			try {
				accessibleContext2 = accessibleContext.getAccessibleChild(i)
						.getAccessibleContext();
			} catch (IndexOutOfBoundsException e) {
				return ret;
			} catch (com.sun.star.lang.IndexOutOfBoundsException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			if (accessibleContext2.getAccessibleRole() == role) {
				ret = accessibleContext2;
				return ret;
			} else
				ret = getAccessibleForRole(accessibleContext2, role);
		}
		return ret;
	}

	// getting the Accessible Table Cache takes a lot of time, so we're caching it
	private static XAccessibleContext accessibleTableCache = null;

	static public Point getCellRangePosition(XFrame frame, CellAddress addr) {
		XWindow win = frame.getContainerWindow();
		XAccessible accessible = (XAccessible) UnoRuntime
				.queryInterface(XAccessible.class, win);
		XAccessibleContext accessibleContext = accessible
				.getAccessibleContext();
		XAccessibleContext table;

		if (SallyUtils.accessibleTableCache == null) {
			SallyUtils.accessibleTableCache = getAccessibleForRole(
					accessibleContext,
					com.sun.star.accessibility.AccessibleRole.TABLE);
		}
		table = SallyUtils.accessibleTableCache;

		XAccessibleTable accessibleTable = (XAccessibleTable) UnoRuntime
				.queryInterface(XAccessibleTable.class, table);
		XAccessibleContext cellToRight = null;

		if (accessibleTable == null) {
			return null;
		}
		try {
			cellToRight = accessibleTable.getAccessibleCellAt(addr.Row, addr.Column).getAccessibleContext();
		} catch (com.sun.star.lang.IndexOutOfBoundsException e) {
			return null;
		} catch (com.sun.star.lang.DisposedException e) {
			accessibleTableCache = null;
			return getCellRangePosition(frame, addr);
		}
		XAccessibleComponent accessibleComponent = (XAccessibleComponent) UnoRuntime
				.queryInterface(XAccessibleComponent.class, cellToRight);

		if (accessibleComponent == null) {
			return null;
		}
		return accessibleComponent.getLocationOnScreen();
	}
}
