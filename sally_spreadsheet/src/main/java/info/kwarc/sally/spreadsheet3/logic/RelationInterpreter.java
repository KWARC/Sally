package info.kwarc.sally.spreadsheet3.logic;

import info.kwarc.sally.spreadsheet3.FormalSpreadsheet;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.model.CellTuple;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.BuilderML;
import info.kwarc.sally.spreadsheet3.ontology.FunctionObject;
import info.kwarc.sally.spreadsheet3.ontology.IOntologyProvider;

public class RelationInterpreter {
	
	/**
	 * Returns the definition of the ontology function that is associated with a relation for the concrete cells.
	 * In example: <apply><csymbol cd="spsht-arith">minus</csymbol><apply><csymbol cd="winograd">RevenuePerYear</csymbol><ci>Year 1984 AD</ci></apply><apply><csymbol cd="winograd">ExpensesPerYear</csymbol><ci>Year 1984 AD</ci><ci>Costtype: Total</ci></apply></apply> 
	 */
	public static String getDefinition(Relation relation, CellTuple cells, FormalSpreadsheet spreadsheet, IOntologyProvider ontologyInterface) {
		String mlDefinition = "";
		FunctionObject function =  ontologyInterface.getFunctionObject(relation.getUri());
		if (function != null) {
			mlDefinition = function.getMLDefinition();
			if (!mlDefinition.isEmpty()) {
				for (int i = 0; i < cells.getSize(); i++) {
					mlDefinition = mlDefinition.replace(
							function.getBuilderML().getVIVaribale(i+1),
							relation.getBlocks().get(i).getValueInterpretation(
									spreadsheet.get(cells.getTuple().get(i)).getValue()));
				}
			} 
		}
		
		return mlDefinition;
	}
	
	/**
	 * Return the interpretation of a relation in respect to the linked ontology function and the values of the associated cells. 
	 * In example: <apply><csymbol cd=\"winograd\">ExpensesPerYear</csymbol><ci>Year 1984 AD</ci><ci>Costtype: Materials</ci></apply>
	 */
	public static String interprete(Relation relation, CellTuple cells, FormalSpreadsheet spreadsheet, BuilderML builderML) {
		String mlInterpretation = "";
		
		if (relation.getRelationType() == Relation.RelationType.FUNCTIONALRELATION) {
		
			mlInterpretation = builderML.getOperatorApplication(Util.getCDFromURI(relation.getUri()), Util.getSymbolFromURI(relation.getUri())) + "\n";
			for (int i = 0; i < cells.getSize()-1; i++) 
				mlInterpretation = mlInterpretation + relation.getBlocks().get(i).getValueInterpretation( spreadsheet.get(cells.getTuple().get(i)).getValue() )  + "\n";
		
			mlInterpretation = mlInterpretation + builderML.getApplicationEnd();
		}
		
		return mlInterpretation;
	}

}
