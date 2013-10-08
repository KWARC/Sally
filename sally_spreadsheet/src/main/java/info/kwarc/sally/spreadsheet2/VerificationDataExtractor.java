package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class VerificationDataExtractor {
	
	static psf.ParserInterface parser = new psf.ParserInterface();
	static String[] mathMLDataTypes = {"omdoc://MathML#Real", "omdoc://MathML#Int", "omdoc://MathML#Bool" };
	
	public static Map<String, List<String>> extractDataTypes(List<Block> blocks, FormalSpreadsheet spreadsheet) {
		Map<String, List<String>> dataTypes = new HashMap<String,List<String>>();
		
		for (Block b : blocks) {
			List<String> values;
			boolean isMathMLDT = false;
			for (String dt : mathMLDataTypes)
				if (dt.equals( b.getOntologyLink().getUri()) )
					isMathMLDT = true;
			if (!isMathMLDT) {
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
		}
		
		return dataTypes;
	}
	
	public static Map<Relation, String> extractCPSimilarFBs(Manager manager, FormalSpreadsheet spreadsheet, BuilderML builderML) {
		Map<Relation, String> mathMLRepresentations = new HashMap<Relation, String>();
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
					String antiunification = Util.antiunifyMathMLFormulae(formulae, domainValues, builderML);
					if (!antiunification.isEmpty()) {
						String equatation = builderML.getOperatorApplication("spsht-arith","equal") + "\n" 
								+ builderML.getOperatorApplication(Util.getCDFromURI(fbRelation.getOntologyLink().getUri()),
										                           Util.getSymbolFromURI(fbRelation.getOntologyLink().getUri())) + "\n";
						int variableCounter = 0;
						for (List<String> dv : domainValues)
							variableCounter = java.lang.Math.max(variableCounter, dv.size());
						for (int i = 0; i < variableCounter; i++)
							equatation = equatation + builderML.getIdentifier("?X" + i) + "\n";
						equatation = equatation + builderML.getApplicationEnd() + "\n" + Util.untagMathObject(antiunification, builderML) + builderML.getApplicationEnd() + "\n";
						mathMLRepresentations.put(r, equatation);
					}
				}
			}
		}
		return mathMLRepresentations;
	}
	
	public static Map<CellSpaceInformation, String> extractMLFormulaRepresentations(Relation rel, Manager manager, FormalSpreadsheet spreadsheet, BuilderML builderML) {
		Map<CellSpaceInformation, String> mlFormulaeRep = new HashMap<CellSpaceInformation, String>();
		if (rel instanceof RelationFunctional) {
			RelationFunctional fbRelation = (RelationFunctional) rel;
			Block fb = fbRelation.getBlocks().get(fbRelation.getBlocks().size()-1);
			
			psf.SemanticMapping mapping = new psf.SemanticMapping();
			Map<CellSpaceInformation, String> interpretation = manager.getCompleteSemanticMapping(spreadsheet);
			for (CellSpaceInformation pos : interpretation.keySet()) 
				mapping.add(pos.getWorksheet(), pos.getRow(), pos.getColumn(), interpretation.get(pos));
			
			for (CellSpaceInformation pos : fb.getCells()) {
				String cellFormula = spreadsheet.get(pos).getFormula();
				String mlFormulaRep = parser.parseFormula(new psf.ParserParameter(cellFormula, pos.getWorksheet(), false, true, false, true, mapping.getMapping())).getMathML();
				
				String equatation = builderML.getOperatorApplication("spsht-arith","equal") + "\n" 
						+ builderML.getOperatorApplication(Util.getCDFromURI(fbRelation.getOntologyLink().getUri()),
								                           Util.getSymbolFromURI(fbRelation.getOntologyLink().getUri())) + "\n";
				
				List<CellTuple> cellRelations = fbRelation.getCellRelationFor(pos);
				if (cellRelations.size() != 1)
					throw new java.lang.IllegalStateException("Number of cell relations for " + pos.toString() + " is not 1.");
				
				CellTuple cellTuple = cellRelations.get(0);
				List<Block> domain = fbRelation.getBlocks();
				domain.remove(domain.size()-1);
				for (int j = 0; j < domain.size(); j++) 
					equatation = equatation + domain.get(j).getOntologyLink().getValueInterpretation(spreadsheet.get(cellTuple.getTuple().get(j)).getValue()) + "\n";
			
				equatation = equatation + builderML.getApplicationEnd() + "\n" + Util.untagMathObject(mlFormulaRep, builderML) + builderML.getApplicationEnd() + "\n";
				mlFormulaeRep.put(pos, equatation);
			}
		}
		return mlFormulaeRep;
	}

}
