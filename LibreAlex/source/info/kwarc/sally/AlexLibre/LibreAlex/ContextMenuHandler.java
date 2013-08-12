package info.kwarc.sally.AlexLibre.LibreAlex;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.sun.star.awt.MenuBar;
import com.sun.star.beans.XPropertySet;
import com.sun.star.ui.ActionTriggerSeparatorType;
import com.sun.star.ui.ContextMenuExecuteEvent;
import com.sun.star.ui.ContextMenuInterceptorAction;
import com.sun.star.ui.XContextMenuInterceptor;
import com.sun.star.uno.UnoRuntime;

public class ContextMenuHandler implements XContextMenuInterceptor {

	Logger log;
	
	public ContextMenuHandler() {
		log = LoggerFactory.getLogger(getClass());
	}
	
	@Override
	public ContextMenuInterceptorAction notifyContextMenuExecute(
			ContextMenuExecuteEvent aEvent) {
		try {
			log.info("Getting actions");
			com.sun.star.container.XIndexContainer xContextMenu = aEvent.ActionTriggerContainer;
			com.sun.star.lang.XMultiServiceFactory xMenuElementFactory = (com.sun.star.lang.XMultiServiceFactory) UnoRuntime
					.queryInterface(
							com.sun.star.lang.XMultiServiceFactory.class,
							xContextMenu);

			if (xMenuElementFactory != null) {
				// create root menu entry and sub menu
				com.sun.star.beans.XPropertySet xRootMenuEntry = (XPropertySet) UnoRuntime
						.queryInterface(
								com.sun.star.beans.XPropertySet.class,
								xMenuElementFactory
								.createInstance("com.sun.star.ui.ActionTrigger"));

				// create a line separator for our new help sub menu
				com.sun.star.beans.XPropertySet xSeparator = (com.sun.star.beans.XPropertySet) UnoRuntime
						.queryInterface(
								com.sun.star.beans.XPropertySet.class,
								xMenuElementFactory
								.createInstance("com.sun.star.ui.ActionTriggerSeparator"));

				Short aSeparatorType = new Short(
						ActionTriggerSeparatorType.LINE);
				xSeparator.setPropertyValue("SeparatorType",
						(Object) aSeparatorType);

				// query sub menu for index container to get access
				com.sun.star.container.XIndexContainer xSubMenuContainer = (com.sun.star.container.XIndexContainer) UnoRuntime
						.queryInterface(
								com.sun.star.container.XIndexContainer.class,
								xMenuElementFactory
								.createInstance("com.sun.star.ui.ActionTriggerContainer"));

				// intialize root menu entry
				xRootMenuEntry.setPropertyValue("Text", new String("Sally"));
				xRootMenuEntry.setPropertyValue("CommandURL", new String(
						"slot:40000"));
				xRootMenuEntry.setPropertyValue("SubContainer",
						(Object) xSubMenuContainer);

				// create menu entries for the new sub menu

				// intialize help/content menu entry
				XPropertySet xMenuEntry = (XPropertySet) UnoRuntime
						.queryInterface(
								XPropertySet.class,
								xMenuElementFactory
								.createInstance("com.sun.star.ui.ActionTrigger"));

				
				xMenuEntry.setPropertyValue("Text", new String(
						"Show Frames"));
				xMenuEntry.setPropertyValue("CommandURL", new String(
						"info.kwarc.sissi.ooalex:showframes"));

				xSubMenuContainer.insertByIndex(0, (Object) xMenuEntry);

				xContextMenu.insertByIndex(0, (Object) xSeparator);

				xContextMenu.insertByIndex(0, (Object) xRootMenuEntry);

				return com.sun.star.ui.ContextMenuInterceptorAction.EXECUTE_MODIFIED;
			}
		} catch (java.lang.Exception ex) {
			log.error(ex.getMessage());
			ex.printStackTrace();
		}
		return com.sun.star.ui.ContextMenuInterceptorAction.IGNORED;
	}
}
