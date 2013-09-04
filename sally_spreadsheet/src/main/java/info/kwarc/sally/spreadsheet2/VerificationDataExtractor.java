package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class VerificationDataExtractor {
	
	static psf.ParserInterface parser = new psf.ParserInterface();
	
	public static Map<String, List<String>> extractDataTypes(List<Block> blocks, FormalSpreadsheet spreadsheet) {
		Map<String, List<String>> dataTypes = new HashMap<String,List<String>>();
		
		for (Block b : blocks) {
			List<String> values;
			if (dataTypes.containsKey(b.getOntologyLink().getUri()))
				values = dataTypes.get(b.getOntologyLink().getUri());
			else {
				values = new ArrayList<String>();
				dataTypes.put(b.getOntologyLink().getUri(), values);
			}
			for (CellSpaceInformation pos : b.getCells()) {
				if ((spreadsheet.get(pos) != null) && 
						!spreadsheet.get(pos).getValue().isEmpty() &&
						!values.contains(b.getOntologyLink().getValueInterpretation( spreadsheet.get(pos).getValue()) ) )
					values.add(b.getOntologyLink().getValueInterpretation( spreadsheet.get(pos).getValue()) );
			}
		}
		
		return dataTypes;
	}
	
	public static List<String> extractCPSimilarFBs(Manager manager, FormalSpreadsheet spreadsheet) {
		List<String> mathMLRepresentations = new ArrayList<String>();
		List<Relation> relations = manager.getAllRelations();
		for (Relation r : relations) {
			if (r instanceof RelationFunctional) {
				RelationFunctional fbRelation = (RelationFunctional) r;
				Block fb = fbRelation.getBlocks().get(fbRelation.getBlocks().size()-1);
				boolean calculatedFb = true;
				for (int i = 0; i < fb.getCells().size(); i++) {
					if (spreadsheet.get(fb.getCells().get(i)).getFormula().isEmpty())
						calculatedFb = false;
				}
				if (calculatedFb) {
					List<String> formulae = new ArrayList<String>();
					List<List<String>> domainValues = new ArrayList<List<String>>();
					
					psf.SemanticMapping mapping = new psf.SemanticMapping();
					Map<CellSpaceInformation, String> interpretation = manager.getCompleteSemanticMapping(spreadsheet);
					for (CellSpaceInformation pos : interpretation.keySet()) 
						mapping.add(pos.getWorksheet(), pos.getRow(), pos.getColumn(), interpretation.get(pos));
					
					for (int i = 0; i < fb.getCells().size(); i++) {
						CellSpaceInformation pos = fb.getCells().get(i);
						psf.ParserParameter p = new psf.ParserParameter(spreadsheet.get(pos).getFormula(), pos.getWorksheet(), false, true, false, true, mapping.getMapping());
						formulae.add(parser.parseFormula(p).getMathML());
						
						List<String> dv = new ArrayList<String>();
						List<CellTuple> cellRelations = fbRelation.getCellRelationFor(pos);
						if (cellRelations.size() != 1)
							throw new java.lang.IllegalStateException("Number of cell relations for " + pos.toString() + " is not 1.");
						
						CellTuple cellTuple = cellRelations.get(0);
						List<Block> domain = fbRelation.getBlocks();
						domain.remove(domain.size()-1);
						for (int j = 0; j < domain.size(); j++) {
							dv.add(domain.get(j).getOntologyLink().getValueInterpretation(spreadsheet.get(cellTuple.getTuple().get(j)).getValue()));
						}
						domainValues.add(dv);
					}
					String antiunification = Util.antiunifyMathMLFormulae(formulae, domainValues);
					if (!antiunification.isEmpty()) {
						String equatation = "<apply>\n<csymbol cd=\"spsht-arith\">equal</csymbol>\n<apply>\n<csymbol cd=\"" + 
								Util.getCDFromURI(fbRelation.getOntologyLink().getUri()) + "\">" + Util.getSymbolFromURI(fbRelation.getOntologyLink().getUri()) +
								"</csymbol>\n";
						int variableCounter = 0;
						for (List<String> dv : domainValues)
							variableCounter = java.lang.Math.max(variableCounter, dv.size());
						for (int i = 0; i < variableCounter; i++)
							equatation = equatation + "<ci>?X" + i + "</ci>\n";
						equatation = equatation + "</apply>\n" + Util.untagMathObject(antiunification);
						mathMLRepresentations.add(equatation);
					}
				}
			}
		}
		return mathMLRepresentations;
	}
	
	

}
