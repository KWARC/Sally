package info.kwarc.sally.spreadsheet3.logic;

import java.util.Map;

import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.model.CellTuple;
import info.kwarc.sally.spreadsheet3.model.ModelException;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.ontology.BuilderML;
import info.kwarc.sally.spreadsheet3.ontology.FunctionObject;
import info.kwarc.sally.spreadsheet3.ontology.IOntologyProvider;

public class RelationInterpreter {
	
	/**
	 * Returns the definition of the ontology function that is associated with a relation for the concrete cells.
	 * In example: <apply><csymbol cd="spsht-arith">minus</csymbol><apply><csymbol cd="winograd">RevenuePerYear</csymbol><ci>Year 1984 AD</ci></apply><apply><csymbol cd="winograd">ExpensesPerYear</csymbol><ci>Year 1984 AD</ci><ci>Costtype: Total</ci></apply></apply> 
	 * @throws ModelException 
	 */
	public static String getDefinition(Relation relation, CellTuple cells, ConcreteSpreadsheet spreadsheet, IOntologyProvider ontologyInterface) throws ModelException {
		String mlDefinition = "";
		FunctionObject function =  ontologyInterface.getFunctionObject(relation.getUri());
		if (function != null) {
		
			mlDefinition = function.getMLDefinition();
			if (!mlDefinition.isEmpty()) {
				
				for (int i = 0; i < function.getArgumentTypes().size(); i++) {
					if (relation.getOntologyLink().isBlockIndex(i) ) {
						int index = relation.getOntologyLink().getBlockIndex(i);
						mlDefinition = mlDefinition.replace(
								function.getBuilderML().getVIVaribale(i),
								relation.getBlocks().get(index).getValueInterpretation(
										spreadsheet.get(cells.getTuple().get(index)).getValue()));
					} else {
						mlDefinition = mlDefinition.replace(
								function.getBuilderML().getVIVaribale(i),
								relation.getOntologyLink().getArgument_(i));
					}			
				}
			} 
		}
		
		return mlDefinition;
	}
	
	/**
	 * Return the interpretation of a relation in respect to the linked ontology function and the values of the associated cells. 
	 * In example: <apply><csymbol cd=\"winograd\">ExpensesPerYear</csymbol><ci>Year 1984 AD</ci><ci>Costtype: Materials</ci></apply>
	 * @throws ModelException 
	 */
	public static String interprete(Relation relation, CellTuple cells, ConcreteSpreadsheet spreadsheet, IOntologyProvider ontologyInterface) throws ModelException {
		return interprete(relation, cells, spreadsheet, ontologyInterface, null);
	}
	
	/**
	 * Return the interpretation of a relation in respect to the linked ontology function and the values of the associated cells. 
	 * In example: <apply><csymbol cd=\"winograd\">ExpensesPerYear</csymbol><ci>Year 1984 AD</ci><ci>Costtype: Materials</ci></apply>
	 * @throws ModelException 
	 */
	public static String interprete(Relation relation, CellTuple cells, ConcreteSpreadsheet spreadsheet, IOntologyProvider ontologyInterface, Map<CellSpaceInformation, String> posToSymbol) throws ModelException {
		String mlInterpretation = "";
		
		BuilderML builderML = ontologyInterface.getBuilderML();
		FunctionObject function =  ontologyInterface.getFunctionObject(relation.getUri());
		
		
		
		if (relation.getRelationType() == Relation.RelationType.FUNCTIONALRELATION) {
		
			mlInterpretation = builderML.getOperatorApplication(Util.getCDFromURI(relation.getUri()), Util.getSymbolFromURI(relation.getUri())) + "\n";
			/*for (int i = 0; i < cells.getSize()-1; i++) 
				if (posToSymbol != null) {
					if (posToSymbol.containsKey(cells.getTuple().get(i)))
						mlInterpretation = mlInterpretation + builderML.getIdentifier(posToSymbol.get(cells.getTuple().get(i))) + "\n";
					else
						throw new java.lang.IllegalArgumentException("No Symbol for position " + cells.getTuple().get(i).toString() + " found. Interpretation not possible.");
				} else
					mlInterpretation = mlInterpretation + relation.getBlocks().get(i).getValueInterpretation( spreadsheet.get(cells.getTuple().get(i)).getValue() )  + "\n";
			*/
			if (function == null)
				System.out.println("No function found for: " + relation.getUri());
			for (int i = 0; i < function.getArgumentTypes().size(); i++) 
				if (relation.getOntologyLink().isBlockIndex(i) ) {
					int index = relation.getOntologyLink().getBlockIndex(i);
					if (posToSymbol != null) {
						if (posToSymbol.containsKey(cells.getTuple().get(index)))
							mlInterpretation = mlInterpretation + builderML.getIdentifier(posToSymbol.get(cells.getTuple().get(index))) + "\n";
						else
							throw new java.lang.IllegalArgumentException("No Symbol for position " + cells.getTuple().get(index).toString() + " found. Interpretation not possible.");
					} else
						mlInterpretation = mlInterpretation + relation.getBlocks().get(index).getValueInterpretation( spreadsheet.get(cells.getTuple().get(index)).getValue() )  + "\n";
				} else 
					mlInterpretation = mlInterpretation + relation.getOntologyLink().getArgument_(i) + "\n";
			mlInterpretation = mlInterpretation + builderML.getApplicationEnd();
		}
		
		return mlInterpretation;
	}

}
