package info.kwarc.sally.model.ontology2;

import com.hp.hpl.jena.rdf.model.Property;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.rdf.model.ResourceFactory;

public class ASM {
	protected static final String uri = "http://www.kwarc.info/sally/asm#";

	/** returns the URI for this schema
    @return the URI for this schema
	 */
	public static String getURI()
	{ return uri; }

	protected static final Resource resource( String local )
	{ return ResourceFactory.createResource( uri + local ); }

	protected static final Property property( String local )
	{ return ResourceFactory.createProperty( uri, local ); }

    public static final Resource FunctionalBlock = resource( "FunctionalBlock" );
    public static final Resource FunctionalInstance = resource( "FunctionalInstance" );
    public static final Resource LegendBlock = resource( "LegendBlock" );
    public static final Resource LegendInstance = resource( "LegendInstance" );

    public static final Property containsFunctionalInstance = property( "containsFunctionalInstance" );
    public static final Property containsLegendInstance = property( "containsLegendInstance" );
    public static final Property partOfFunctionalBlock = property( "partOfFunctionalBlock" );
    public static final Property partOfLegendBlock = property( "partOfLegendBlock" );

    public static final Property valueOf = property( "valueOf" );
    public static final Property linkedTo = property( "linkedTo" );
    public static final Property partOfFile = property( "partOfFile" );

}
