package info.kwarc.sissi.model.document.cad;

import com.hp.hpl.jena.rdf.model.Property;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.rdf.model.ResourceFactory;

public class ACM {
	protected static final String uri = "http://www.kwarc.info/sally/acm#";

	/** returns the URI for this schema
    @return the URI for this schema
	 */
	public static String getURI()
	{ return uri; }

	protected static final Resource resource( String local )
	{ return ResourceFactory.createResource( uri + local ); }

	protected static final Property property( String local )
	{ return ResourceFactory.createProperty( uri, local ); }

    public static final Resource CADObject = resource( "CADObject" );
    
    public static final Property partOf = property( "partOf" );

    public static final Property valueOf = property( "valueOf" );
    public static final Property partOfFile = property( "partOfFile" );

}
