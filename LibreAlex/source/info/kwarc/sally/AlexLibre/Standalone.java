package info.kwarc.sally.AlexLibre;

import info.kwarc.sally.AlexLibre.Sally.SallyManager;

import java.io.IOException;

import ooo.connector.BootstrapSocketConnector;

import com.sun.star.comp.helper.BootstrapException;
import com.sun.star.frame.XDesktop;
import com.sun.star.uno.Exception;
import com.sun.star.uno.UnoRuntime;
import com.sun.star.uno.XComponentContext;

public class Standalone {

	public static void main(String[] args) {
		try {
			SallyManager.getInstance();
			String oooExeFolder = "D:\\opt\\libre4\\program";
			XComponentContext xContext = BootstrapSocketConnector.bootstrap(oooExeFolder);
			// get the remote office service manager
			com.sun.star.lang.XMultiComponentFactory xMCF =
					xContext.getServiceManager();

			Object oDesktop = xMCF.createInstanceWithContext(
					"com.sun.star.frame.Desktop", xContext);

			XDesktop xDesktop = (XDesktop) UnoRuntime.queryInterface(
					XDesktop.class, oDesktop);

			com.sun.star.frame.XComponentLoader xCompLoader =
					(com.sun.star.frame.XComponentLoader)
					UnoRuntime.queryInterface(
							com.sun.star.frame.XComponentLoader.class, oDesktop);

//			String sUrl = "/home/costea/kwarc/sissi/doc/papers/Interact_2013/spsht/PipeEndPricing_v4.xlsm";
			String sUrl = "D:\\kwarc\\spsht\\PipeEndPricing_v4.xlsm";
			if ( sUrl.indexOf("private:") != 0) {
				java.io.File sourceFile = new java.io.File(sUrl);
				StringBuffer sbTmp = new StringBuffer("file:///");
				sbTmp.append(sourceFile.getCanonicalPath().replace('\\', '/'));
				sUrl = sbTmp.toString();
			}

			// Load a Writer document, which will be automaticly displayed
			com.sun.star.lang.XComponent xComp = xCompLoader.loadComponentFromURL(
					sUrl, "_blank", 0, new com.sun.star.beans.PropertyValue[0]);

			try {
				SallyManager.getInstance().startSally(xContext);
			} catch (java.lang.Exception e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		} catch (BootstrapException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

}
