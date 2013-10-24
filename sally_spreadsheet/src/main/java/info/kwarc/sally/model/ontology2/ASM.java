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

    public static final Resource Block = resource( "Block" );
    public static final Resource Relation = resource( "Relation" );
    public static final Resource AbstractSpreadsheetModelType = resource("");
    
    public static final Property hasArgs = property( "hasArgs" );
    public static final Property hasURL = property( "hasURL" );

    public static final Property hasSheet = property( "hasSheet" );
    public static final Property hasStartRow = property( "hasStartRow" );
    public static final Property hasStartCol = property( "hasStartCol" );
    public static final Property hasEndRow = property( "hasEndRow" );
    public static final Property hasEndCol = property( "hasEndCol" );
    
    public static final Property blockID = property( "blockid" );
    public static final Property relType  = property( "relationType" );
    public static final Property partOfFile = property( "partOfFile" );
    public static final Property partOfASM= property( "partOfASM" );

}
