package info.kwarc.sally.pivot.ontology;

import com.hp.hpl.jena.rdf.model.Property;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.rdf.model.ResourceFactory;

public class Pivot {
	protected static final String uri = "http://www.kwarc.info/sally/pivot#";

	/** returns the URI for this schema
    @return the URI for this schema
	 */
	public static String getURI()
	{ return uri; }

	protected static final Resource resource( String local )
	{ return ResourceFactory.createResource( uri + local ); }

	protected static final Property property( String local )
	{ return ResourceFactory.createProperty( uri, local ); }

	public static final Resource knowledgeUnit = resource("knowledgeUnit");
	public static final Resource softwareObject = resource("softwareObject");

	public static final Property hasName = property( "hasName" );
	public static final Property isRealized = property( "isRealized" );
	public static final Property partOfKnowledgeUnit = property( "partOfKnowledgeUnit" );
	public static final Property partOfFile = property( "partOfFile" );
	public static final Property hasURI = property( "hasURI" );
}