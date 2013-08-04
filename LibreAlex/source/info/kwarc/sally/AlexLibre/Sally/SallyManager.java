package info.kwarc.sally.AlexLibre.Sally;

import info.kwarc.sally.AlexLibre.LibreAlex.ContextMenuHandler;

import java.util.HashMap;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.sun.star.container.XEnumeration;
import com.sun.star.frame.XController;
import com.sun.star.frame.XDesktop;
import com.sun.star.frame.XFrame;
import com.sun.star.lang.XComponent;
import com.sun.star.sheet.XSpreadsheetDocument;
import com.sun.star.ui.XContextMenuInterception;
import com.sun.star.uno.UnoRuntime;
import com.sun.star.uno.XComponentContext;

public class SallyManager {

	/**
	 * SingletonHolder is loaded on the first execution of Singleton.getInstance() 
	 * or the first access to SingletonHolder.INSTANCE, not before.
	 */
	private static class SingletonHolder { 
		public static final SallyManager INSTANCE = new SallyManager();
	}

	public static SallyManager getInstance() {
		return SingletonHolder.INSTANCE;
	}

	boolean started;
	private ContextMenuHandler contextMenuHandler;
	
	XComponentContext m_xContext;

	Logger log;

	HashMap<XSpreadsheetDocument, SpreadsheetDoc> docMap;

	private SallyManager() {
		started = false;
		log = LoggerFactory.getLogger(this.getClass());
		docMap = new HashMap<XSpreadsheetDocument, SpreadsheetDoc>();
		contextMenuHandler = new ContextMenuHandler();
	}

	public boolean getStarted() {
		return started;
	}

	public void refreshDocList() throws Exception {
		if (!started)
			return;
		XDesktop xDesktop = SallyUtils.getDesktop(m_xContext);
		XEnumeration r = xDesktop.getComponents().createEnumeration();
		log.info("Refreshing doc list");

		while (r.hasMoreElements()) {
			XComponent xcomponent = UnoRuntime.queryInterface(XComponent.class, r.nextElement());

			XSpreadsheetDocument xSpreadsheetDocument = (XSpreadsheetDocument) UnoRuntime
					.queryInterface(XSpreadsheetDocument.class,
							xcomponent);

			if (docMap.containsKey(xSpreadsheetDocument)) {
				log.info("Ignoring "+SallyUtils.getDocumentName(xSpreadsheetDocument));
				continue;
			}
			log.info("Starting to look after "+SallyUtils.getDocumentName(xSpreadsheetDocument));
			docMap.put(xSpreadsheetDocument, new SpreadsheetDoc(xSpreadsheetDocument));
		}
	}

	private void addContextMenu(XFrame m_xFrame) {
		XController xController = m_xFrame.getController();
		if (xController != null) {
			XContextMenuInterception xContextMenuInterception = (com.sun.star.ui.XContextMenuInterception) UnoRuntime
					.queryInterface(
							com.sun.star.ui.XContextMenuInterception.class,
							xController);
			xContextMenuInterception.registerContextMenuInterceptor(contextMenuHandler);
		}
	}
	
	public void removeContextMenu(XFrame m_xFrame) {
		XController xController = m_xFrame.getController();
		if (xController != null) {
			XContextMenuInterception xContextMenuInterception = (com.sun.star.ui.XContextMenuInterception) UnoRuntime
					.queryInterface(
							com.sun.star.ui.XContextMenuInterception.class,
							xController);
			xContextMenuInterception.releaseContextMenuInterceptor(contextMenuHandler);
		}
	}

	public void startSally(XComponentContext m_xContext) {
		this.m_xContext = m_xContext;
		if (started)
			return;
		started = true;
		
		try {
			XDesktop xDesktop = SallyUtils.getDesktop(m_xContext);
			addContextMenu(xDesktop.getCurrentFrame());
			
			refreshDocList();
		} catch (Exception e) {
			e.printStackTrace();
			log.error("Exception "+e.getMessage());
		}
	}

	public void stopSally(XComponentContext m_xContext) {
		if (!started)
			return;
		started = false;
		this.m_xContext = m_xContext;

		try {
			XDesktop xDesktop = SallyUtils.getDesktop(m_xContext);
			removeContextMenu(xDesktop.getCurrentFrame());
		} catch (Exception e) {
			log.error("Exception "+e.getMessage());
		}
	}
	
	public void showFrames() {
		log.info("showing frames");
	}
}
