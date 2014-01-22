package info.kwarc.sally.AlexLibre.Sally;

import info.kwarc.sally.AlexLibre.LibreAlex.ContextMenuHandler;
import info.kwarc.sally.AlexLibre.Sally.handlers.DoSelect;
import info.kwarc.sally.AlexLibre.Sally.handlers.GetDataRange;

import java.util.HashMap;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.SallyFrame;

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
	SallyCommunication comm;

	public XComponentContext getContext() {
		return m_xContext;
	}

	Logger log;
	ShareJSAdapter sharejsAdapter;

	HashMap<XSpreadsheetDocument, SpreadsheetDoc> docMap;

	private SallyManager() {
		started = false;
		log = LoggerFactory.getLogger(this.getClass());
		docMap = new HashMap<XSpreadsheetDocument, SpreadsheetDoc>();
		sharejsAdapter = new ShareJSAdapter("http://localhost:7007");
		contextMenuHandler = new ContextMenuHandler();
		comm = new SallyCommunication("http://localhost", 8181);
		comm.addHandler(new GetDataRange());
		comm.addHandler(new DoSelect());
		comm.start();
	}

	public boolean getStarted() {
		return started;
	}

	public SpreadsheetDoc getSpreadsheetDoc(String fileName) {
		for (XSpreadsheetDocument doc : docMap.keySet()) {
			if (SallyUtils.getDocumentName(doc).equals(fileName)) {
				return docMap.get(doc);
			}
		}
		return null;
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
			
			com.sun.star.frame.XModel xModel = (com.sun.star.frame.XModel) UnoRuntime
					.queryInterface(com.sun.star.frame.XModel.class,
							xSpreadsheetDocument);

			
			addContextMenu(xModel.getCurrentController());

			log.info("Starting to look after "+SallyUtils.getDocumentName(xSpreadsheetDocument));
			docMap.put(xSpreadsheetDocument, new SpreadsheetDoc(xSpreadsheetDocument, comm, sharejsAdapter));
		}
	}

	private void addContextMenu(XController xController) {
		XContextMenuInterception xContextMenuInterception = (com.sun.star.ui.XContextMenuInterception) UnoRuntime
				.queryInterface(
						com.sun.star.ui.XContextMenuInterception.class,
						xController);
		xContextMenuInterception.registerContextMenuInterceptor(contextMenuHandler);
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
		log.info("start context = "+m_xContext);
		if (started)
			return;
		started = true;

		try {
			XDesktop xDesktop = SallyUtils.getDesktop(m_xContext);

			refreshDocList();
		} catch (Exception e) {
			e.printStackTrace();
			log.error("Exception "+e.getMessage());
		}
	}

	public void stopSally(XComponentContext m_xContext) {
		if (!started)
			return;
		log.info("end context = "+m_xContext);
		started = false;
		this.m_xContext = m_xContext;

		try {
			XDesktop xDesktop = SallyUtils.getDesktop(m_xContext);
			removeContextMenu(xDesktop.getCurrentFrame());
		} catch (Exception e) {
			log.error("Exception "+e.getMessage());
		}
	}

	public void showFrames(XComponentContext m_xContext) {
		log.info("frames context = "+m_xContext);
		try {
			XDesktop xDesktop = SallyUtils.getDesktop(m_xContext);
			log.info("got desktop");

			XSpreadsheetDocument xSpreadsheetDocument = (XSpreadsheetDocument) UnoRuntime
					.queryInterface(XSpreadsheetDocument.class,
							xDesktop.getCurrentComponent());

			log.info("sending frame request ");
			comm.sendMessage("/service/alex/sallyFrame", SallyFrame.newBuilder().setFileName(SallyUtils.getDocumentName(xSpreadsheetDocument)).build());
		} catch (Exception e) {
			e.printStackTrace();
			log.error(e.getMessage());
		}
	}
}
