package info.kwarc.sally.model.ontology2;

import com.hp.hpl.jena.rdf.model.Property;
import com.hp.hpl.jena.rdf.model.Resource;
import com.hp.hpl.jena.rdf.model.ResourceFactory;

public class CSM {
	protected static final String uri = "http://www.kwarc.info/sally/csm#";

	/** returns the URI for this schema
    @return the URI for this schema
	 */
	public static String getURI()
	{ return uri; }

	protected static final Resource resource( String local )
	{ return ResourceFactory.createResource( uri + local ); }

	protected static final Property property( String local )
	{ return ResourceFactory.createProperty( uri, local ); }

    public static final Resource Cell = resource( "Cell" );
    public static final Resource CellRange = resource( "CellRange" );
    public static final Resource Sheet = resource( "Sheet" );
    public static final Resource Workbook = resource( "Workbook" );

    public static final Property containsCell = property( "containsCell" );
    public static final Property containsSheet = property( "containsSheet" );

    public static final Property partOfSheet = property( "partOfSheet" );
    public static final Property partOfWorkbook = property( "partOfWorkbook" );
    
    public static final Property hasStartRow = property( "hasStartRow" );
    public static final Property hasEndRow = property( "hasEndRow" );
    public static final Property hasStartCol = property( "hasStartCol" );
    public static final Property hasEndCol= property( "hasEndCol" );

}
