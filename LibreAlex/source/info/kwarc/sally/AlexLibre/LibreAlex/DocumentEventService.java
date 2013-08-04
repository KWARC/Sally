package info.kwarc.sally.AlexLibre.LibreAlex;

import info.kwarc.sally.AlexLibre.Sally.SallyManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.sun.star.beans.NamedValue;
import com.sun.star.lang.IllegalArgumentException;
import com.sun.star.lang.XSingleComponentFactory;
import com.sun.star.lib.uno.helper.Factory;
import com.sun.star.lib.uno.helper.WeakBase;
import com.sun.star.registry.XRegistryKey;
import com.sun.star.task.XJob;
import com.sun.star.uno.Exception;
import com.sun.star.uno.XComponentContext;

public final class DocumentEventService extends WeakBase
   implements com.sun.star.lang.XServiceInfo,
              XJob
{
    private final XComponentContext m_xContext;
    private static final String m_implementationName = DocumentEventService.class.getName();
    private static final String[] m_serviceNames = {
        "info.kwarc.sally.LibreAlex.DocumentEventService" };

    Logger log;

    public DocumentEventService( XComponentContext context )
    {
    	log = LoggerFactory.getLogger(getClass());
        m_xContext = context;
    };

    public static XSingleComponentFactory __getComponentFactory( String sImplementationName ) {
        XSingleComponentFactory xFactory = null;

        if ( sImplementationName.equals( m_implementationName ) )
            xFactory = Factory.createComponentFactory(DocumentEventService.class, m_serviceNames);
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

	@Override
	public Object execute(NamedValue[] arg0) throws IllegalArgumentException,
			Exception {
		try {
			SallyManager.getInstance().refreshDocList();
		} catch (java.lang.Exception e) {
			e.printStackTrace();
		}
		return null;
	}

}
