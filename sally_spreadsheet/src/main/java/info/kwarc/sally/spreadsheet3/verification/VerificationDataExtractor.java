package info.kwarc.sally.spreadsheet3.verification;

import info.kwarc.sally.spreadsheet3.Manager;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.CellTuple;
import info.kwarc.sally.spreadsheet3.model.ModelException;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.BuilderML;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * The VerificationDataExtractor extracts information about the datatypes, cp-similar blocks and formulae from an annotated spreadsheet.
 * @author cliguda
 *
 */
public class VerificationDataExtractor {
	
	static psf.ParserInterface parser = new psf.ParserInterface();
	//static String[] stdDataTypes = {"omdoc://MathML#Real", "omdoc://MathML#Int", "omdoc://MathML#Bool" };
	
	/**
	 * Extract information about data types (ontology objects) from an annotated spreadsheets.
	 * @param blocks A mapping from blocks to their ontology type (URI).
	 * @param spreadsheet A concrete spreadsheet to get the values from cells.
	 * @return
	 * @throws ModelException
	 */
	public static List<DataSymbolInformation> extractDataTypes(Map<Block, String> blocks, ConcreteSpreadsheet spreadsheet) throws ModelException {
		
		List<DataSymbolInformation> dataObjects = new ArrayList<DataSymbolInformation>();
		int symbolID = 0;
		for (Block b : blocks.keySet()) {
			for (CellSpaceInformation pos : b.getCells()) {
				if ((spreadsheet.get(pos) != null) && !spreadsheet.get(pos).getValue().isEmpty()) {
					dataObjects.add(new DataSymbolInformation(blocks.get(b), b.getValueInterpretation( spreadsheet.get(pos).getValue()), pos, symbolID));
					symbolID++;
				}
			}
		}
		
		return dataObjects;
	}
	
	
	public static List<CPSimilarBlockData> extractCPSimilarFBs(Manager manager) throws ModelException {
		List<CPSimilarBlockData> cpSimilarBlockData = new ArrayList<CPSimilarBlockData>();
		//Map<Relation, String> mathMLRepresentations = new HashMap<Relation, String>();
		//List<Relation> relations = manager.getAllRelations();
		for (Relation fbRelation : manager.getModel().getAllRelations()) {
			if (fbRelation.getRelationType().equals(Relation.RelationType.FUNCTIONALRELATION)) {
		
				Block fb = fbRelation.getBlocks().get(fbRelation.getBlocks().size()-1);
				boolean calculatedFb = true;
				for (int i = 0; i < fb.getCells().size(); i++) {
					if (manager.getSpreadsheet().get(fb.getCells().get(i)).getFormula().isEmpty())
						calculatedFb = false;
				}
				if (calculatedFb) {
					List<String> formulae = new ArrayList<String>();
					List<List<String>> domainValues = new ArrayList<List<String>>();
					
					psf.SemanticMapping mapping = new psf.SemanticMapping();
					Map<CellSpaceInformation, String> interpretation = manager.getModel().getCompleteSemanticMapping(manager.getSpreadsheet(), manager.getOntology());
					for (CellSpaceInformation pos : interpretation.keySet()) 
						mapping.add(pos.getWorksheet(), pos.getRow(), pos.getColumn(), interpretation.get(pos));
					
					for (int i = 0; i < fb.getCells().size(); i++) {
						CellSpaceInformation pos = fb.getCells().get(i);
						psf.ParserParameter p = new psf.ParserParameter(manager.getSpreadsheet().get(pos).getFormula(), pos.getWorksheet(), false, true, false, true, mapping.getMapping());
						formulae.add(parser.parseFormula(p).getMathML());
						
						List<String> dv = new ArrayList<String>();
						List<CellTuple> cellRelations = fbRelation.getCellRelationFor(pos);
						if (cellRelations.size() != 1)
							throw new java.lang.IllegalStateException("Number of cell relations for " + pos.toString() + " is not 1.");
						
						CellTuple cellTuple = cellRelations.get(0);
						List<Block> domain = fbRelation.getBlocks();
						domain.remove(domain.size()-1);
						for (int j = 0; j < domain.size(); j++) {
							dv.add(domain.get(j).getValueInterpretation(manager.getSpreadsheet().get(cellTuple.getTuple().get(j)).getValue()));
						}
						domainValues.add(dv);
					}
					BuilderML builderML = manager.getOntology().getBuilderML();
					String antiunification = Util.antiunifyMathMLFormulae(formulae, domainValues, builderML);
					if (!antiunification.isEmpty()) {
						String equatation = builderML.getOperatorApplication("spsht-arith","equal") + "\n" 
								+ builderML.getOperatorApplication(Util.getCDFromURI(fbRelation.getUri()),
										                           Util.getSymbolFromURI(fbRelation.getUri())) + "\n";
						/*int variableCounter = 0;
						for (List<String> dv : domainValues)
							variableCounter = java.lang.Math.max(variableCounter, dv.size());
						for (int i = 0; i < variableCounter; i++)
							equatation = equatation + builderML.getIdentifier("?X" + i) + "\n";*/
						for (int i = 0; i < manager.getOntology().getFunctionObject(fbRelation.getUri()).getArgumentTypes().size(); i++ )
							equatation = equatation + builderML.getVIVaribale(i) + "\n";
						equatation = equatation + builderML.getApplicationEnd() + "\n" + Util.untagMathObject(antiunification, builderML) + builderML.getApplicationEnd() + "\n";
						//mathMLRepresentations.put(fbRelation, equatation);
						cpSimilarBlockData.add(new CPSimilarBlockData(fbRelation, equatation, Util.getConstantArguments(domainValues)));
					}
				}
			}
		}
		return cpSimilarBlockData;
	}
	
	/**
	 * Extracts a ml representation for a functional relation.
	 * For each cell the corresponding function declaration (e.g. profitPerYear(1984) ) and definition (Revenues(1984)-TotalCosts(1984)) are determined and used to generate a ML representation.
	 * In example a MathML representation for profitPerYear(1984) = Revenues(1984)-TotalCosts(1984).
	 * @param fbRelation
	 * @param manager
	 * @return
	 * @throws ModelException
	 */
	public static Map<CellSpaceInformation, String> extractMLFormulaRepresentations(Relation fbRelation, Manager manager) throws ModelException {
		Map<CellSpaceInformation, String> mlFormulaeRep = new HashMap<CellSpaceInformation, String>();
		if (fbRelation.getRelationType().equals(Relation.RelationType.FUNCTIONALRELATION)) {
			Block fb = fbRelation.getBlocks().get(fbRelation.getBlocks().size()-1);
			
			psf.SemanticMapping mapping = new psf.SemanticMapping();
			Map<CellSpaceInformation, String> interpretation = manager.getModel().getCompleteSemanticMapping( manager.getSpreadsheet(), manager.getOntology());
			for (CellSpaceInformation pos : interpretation.keySet()) 
				mapping.add(pos.getWorksheet(), pos.getRow(), pos.getColumn(), interpretation.get(pos));
			
			BuilderML builderML = manager.getOntology().getBuilderML();
			for (CellSpaceInformation pos : fb.getCells()) {
				String cellFormula = manager.getSpreadsheet().get(pos).getFormula();
				String mlFormulaRep = parser.parseFormula(new psf.ParserParameter(cellFormula, pos.getWorksheet(), false, true, false, true, mapping.getMapping())).getMathML();
				
				String equatation = builderML.getOperatorApplication("spsht-arith","equal") + "\n" 
						+ builderML.getOperatorApplication(Util.getCDFromURI(fbRelation.getUri()),
								                           Util.getSymbolFromURI(fbRelation.getUri())) + "\n";
				
				List<CellTuple> cellRelations = fbRelation.getCellRelationFor(pos);
				if (cellRelations.size() != 1)
					throw new java.lang.IllegalStateException("Number of cell relations for " + pos.toString() + " is not 1.");
				
				CellTuple cellTuple = cellRelations.get(0);
				List<Block> domain = fbRelation.getBlocks();
				domain.remove(domain.size()-1);
				for (int j = 0; j < domain.size(); j++) 
					equatation = equatation + domain.get(j).getValueInterpretation( manager.getSpreadsheet().get(cellTuple.getTuple().get(j)).getValue()) + "\n";
			
				equatation = equatation + builderML.getApplicationEnd() + "\n" + Util.untagMathObject(mlFormulaRep, builderML) + builderML.getApplicationEnd() + "\n";
				mlFormulaeRep.put(pos, equatation);
			}
		}
		return mlFormulaeRep;
	}

}
