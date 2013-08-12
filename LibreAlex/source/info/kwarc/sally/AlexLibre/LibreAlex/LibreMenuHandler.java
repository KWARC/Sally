package info.kwarc.sally.AlexLibre.LibreAlex;

import info.kwarc.sally.AlexLibre.Sally.SallyManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.sun.star.frame.DispatchDescriptor;
import com.sun.star.frame.XDispatch;
import com.sun.star.frame.XStatusListener;
import com.sun.star.lang.XSingleComponentFactory;
import com.sun.star.lib.uno.helper.Factory;
import com.sun.star.lib.uno.helper.WeakBase;
import com.sun.star.registry.XRegistryKey;
import com.sun.star.uno.Exception;
import com.sun.star.uno.XComponentContext;
import com.sun.star.util.URL;


public final class LibreMenuHandler extends WeakBase
implements com.sun.star.lang.XServiceInfo,
info.kwarc.sally.LibreAlex.XLibreAlex,
com.sun.star.frame.XDispatch, com.sun.star.frame.XDispatchProvider, com.sun.star.lang.XInitialization
{
	private final XComponentContext m_xContext;
	private static final String m_implementationName = LibreMenuHandler.class.getName();
	private static final String[] m_serviceNames = {
	"info.kwarc.sally.LibreAlex.LibreMenuHandler" };

	Logger log;

	public LibreMenuHandler( XComponentContext context )
	{
		m_xContext = context;
		log = LoggerFactory.getLogger(this.getClass());
	};

	public static XSingleComponentFactory __getComponentFactory( String sImplementationName ) {
		XSingleComponentFactory xFactory = null;

		if ( sImplementationName.equals( m_implementationName ) )
			xFactory = Factory.createComponentFactory(LibreMenuHandler.class, m_serviceNames);
		return xFactory;
	}

	public static boolean __writeRegistryServiceInfo( XRegistryKey xRegistryKey ) {
		return Factory.writeRegistryServiceInfo(m_implementationName,
				m_serviceNames,
				xRegistryKey);
	}

	// com.sun.star.lang.XServiceInfo:
	public String getImplementationName() {
		return m_implementationName;
	}

	public boolean supportsService( String sService ) {
		int len = m_serviceNames.length;

		for( int i=0; i < len; i++) {
			if (sService.equals(m_serviceNames[i]))
				return true;
		}
		return false;
	}

	public String[] getSupportedServiceNames() {
		return m_serviceNames;
	}

	// XDispatchProvider
	/**
	 * Used to dispatch queries. You can add new items for the context menu or
	 * other menus here as long as you provide a function to be executed for the
	 * corresponding option.
	 */
	@Override
	public XDispatch queryDispatch(/* IN */com.sun.star.util.URL aURL,
			/* IN */String sTargetFrameName,
			/* IN */int iSearchFlags) {
		XDispatch xRet = null;
		log.info("Query dispatching "+aURL.Path+" "+aURL.Protocol);
		if (aURL.Protocol.compareTo("info.kwarc.sissi.ooalex:") == 0) {
			if (aURL.Path.compareTo("start") == 0) {
				xRet = this;				
			}
			if (aURL.Path.compareTo("stop") == 0) {
				xRet = this;
			}
			if (aURL.Path.compareTo("showframes") == 0) {
				xRet = this;
			}			
		}

		return xRet;
	}

	@Override
	public XDispatch[] queryDispatches(DispatchDescriptor[] seqDescripts) {
		int nCount = seqDescripts.length;
		XDispatch[] lDispatcher = new XDispatch[nCount];

		for (int i = 0; i < nCount; ++i)
			lDispatcher[i] = queryDispatch(seqDescripts[i].FeatureURL,
					seqDescripts[i].FrameName, seqDescripts[i].SearchFlags);

		return lDispatcher;
	}

	@Override
	public void addStatusListener(XStatusListener arg0, URL arg1) {

	}

	@Override
	public void dispatch(/* IN */com.sun.star.util.URL aURL,
			/* IN */com.sun.star.beans.PropertyValue[] aArguments) {
		if (aURL.Protocol.compareTo("info.kwarc.sissi.ooalex:") == 0) {
			/*
			 * Start Sally if the start option is pressed.
			 */
			if (aURL.Path.compareTo("start") == 0) {
				log.debug("dispatching start in "+this+" with "+aArguments.length);
				SallyManager.getInstance().startSally(m_xContext);
			}

			/*
			 * Start Sally if the start option is pressed.
			 */
			if (aURL.Path.compareTo("stop") == 0) {
				log.debug("dispatching stop in "+this+" with "+aArguments.length);
				SallyManager.getInstance().stopSally(m_xContext);
			}

			/*
			 * Start Sally if the start option is pressed.
			 */
			if (aURL.Path.compareTo("showframes") == 0) {
				log.info("Showing frames");
				SallyManager.getInstance().showFrames(m_xContext);
			}
		}
	}


	@Override
	public void removeStatusListener(XStatusListener arg0, URL arg1) {

	}

	@Override
	public void initialize(Object[] object) throws Exception {

	}

}
