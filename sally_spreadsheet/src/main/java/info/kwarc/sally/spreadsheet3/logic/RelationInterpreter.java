package info.kwarc.sally.spreadsheet3.logic;

import info.kwarc.sally.spreadsheet2.Util;
import info.kwarc.sally.spreadsheet3.FormalSpreadsheet;
import info.kwarc.sally.spreadsheet3.model.CellTuple;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.BuilderML;
import info.kwarc.sally.spreadsheet3.ontology.FunctionObject;
import info.kwarc.sally.spreadsheet3.ontology.Interface;

public class RelationInterpreter {
	
	public static String getDefinition(Relation relation, CellTuple cells, FormalSpreadsheet spreadsheet, Interface ontologyInterface) {
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
	
	public static String interprete(Relation relation, CellTuple cells, FormalSpreadsheet spreadsheet, BuilderML builderML) {
		String mlInterpretation = "";
		
		if (relation.getRelationType() == Relation.FUNCTIONALRELATION) {
		
			mlInterpretation = builderML.getOperatorApplication(Util.getCDFromURI(relation.getUri()), Util.getSymbolFromURI(relation.getUri())) + "\n";
			for (int i = 0; i < cells.getSize()-1; i++) 
				mlInterpretation = mlInterpretation + relation.getBlocks().get(i).getValueInterpretation( spreadsheet.get(cells.getTuple().get(i)).getValue() )  + "\n";
		
			mlInterpretation = mlInterpretation + builderML.getApplicationEnd();
		}
		
		return mlInterpretation;
	}

}
