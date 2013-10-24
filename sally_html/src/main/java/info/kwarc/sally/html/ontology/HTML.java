package info.kwarc.sally.html.ontology;

import com.hp.hpl.jena.rdf.model.Property;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.rdf.model.ResourceFactory;

public class HTML {
	protected static final String uri = "http://www.kwarc.info/sally/html#";

	/** returns the URI for this schema
    @return the URI for this schema
	 */
	public static String getURI()
	{ return uri; }

	protected static final Resource resource( String local )
	{ return ResourceFactory.createResource( uri + local ); }

	protected static final Property property( String local )
	{ return ResourceFactory.createProperty( uri, local ); }

    public static final Property hasHTMLID = property( "hasHTMLID" );
}
