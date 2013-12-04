package info.kwarc.sally.spreadsheet3.ontology;

import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.PropertyName;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.model.Relation.RelationType;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SemanticModelManager {

	Map<String, List<String>> semanticValues;
	Map<String, List<Block>> uriToBlocks;
	
	public SemanticModelManager() {
		semanticValues = new HashMap<String, List<String>>();
		uriToBlocks = new HashMap<String, List<Block>>();
	}
	
	public void createSemanticValues(List<Relation> relations, ConcreteSpreadsheet spreadsheet) {
		for (Relation rel : relations) {
			if (rel.getRelationType().equals(RelationType.TYPERELATION)) {
				for (Block block : rel.getBlocks()) {
					// Checking URI -> Block link
					List<Block> blocks;
					if (uriToBlocks.containsKey(rel.getUri()))
						blocks = uriToBlocks.get(rel.getUri());
					else {
						blocks = new ArrayList<Block>();
						uriToBlocks.put(rel.getUri(), blocks);
					}
					if (!blocks.contains(block))
						blocks.add(block);
					
					// Checking URI -> semantic values
					List<String> values;
					if (semanticValues.containsKey(rel.getUri()))
						values = semanticValues.get(rel.getUri());
					else {
						values = new ArrayList<String>();
						semanticValues.put(rel.getUri(), values);
					}
					for (CellSpaceInformation pos : block.getCells()) {
						String cellValue = spreadsheet.get(pos).getValue();
						if (!cellValue.isEmpty()) {
							String semanticValue = block.getValueInterpretation(cellValue);
							if (!values.contains(semanticValue))
								values.add(semanticValue);
						}
					}
				}
			}
		}
	}
	
	public SemanticModelMessage checkBlockForCompleteness(Block block, String uri, ConcreteSpreadsheet spreadsheet) {
		SemanticModelMessage msg;
		
		if (!block.hasProperty(PropertyName.COMPLETESEMANTICBLOCK) ||
			block.getProperty(PropertyName.COMPLETESEMANTICBLOCK).equals("false") )
			msg = new SemanticModelMessage(SemanticModelMessage.MessageType.UNCHECKED, block.getId());
		else if (!semanticValues.containsKey(uri)) 
			msg = new SemanticModelMessage(SemanticModelMessage.MessageType.ERROR, block.getId());
		else {
			List<String> values = new ArrayList<String>();
			for (CellSpaceInformation pos : block.getCells()) {
				String cellValue = spreadsheet.get(pos).getValue();
				if (!cellValue.isEmpty()) {
					String semanticValue = block.getValueInterpretation(cellValue);
					if (!values.contains(semanticValue))
						values.add(semanticValue);
				}
			}
			if (semanticValues.get(uri).equals(values))
				msg = new SemanticModelMessage(SemanticModelMessage.MessageType.VALID, block.getId());
			else
				msg = new SemanticModelMessage(SemanticModelMessage.MessageType.INCOMPLETEBLOCK, block.getId());
		} 
			
		return msg;
	}
	
	public List<String> getAllValuesForURI(String uri) {
		if (semanticValues.containsKey(uri))
			return new ArrayList<String>(semanticValues.get(uri));
		else
			return new ArrayList<String>();
	}
	
	public List<Block> getAllBlocksForURI(String uri) {
		if (uriToBlocks.containsKey(uri))
			return new ArrayList<Block>(uriToBlocks.get(uri));
		else
			return new ArrayList<Block>();
	}
	
}
