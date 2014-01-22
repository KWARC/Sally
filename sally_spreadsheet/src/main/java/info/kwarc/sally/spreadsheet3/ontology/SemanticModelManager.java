package info.kwarc.sally.spreadsheet3.ontology;

import info.kwarc.sally.spreadsheet3.ConcreteSpreadsheet;
import info.kwarc.sally.spreadsheet3.Message;
import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.ModelException;
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
	
	public void createSemanticValues(List<Relation> relations, ConcreteSpreadsheet spreadsheet) throws ModelException {
		semanticValues = new HashMap<String, List<String>>();
		uriToBlocks = new HashMap<String, List<Block>>();
		
		for (Relation rel : relations)
			try {
				updateSemanticValues(rel, spreadsheet);
			} catch (ModelException e) {
				semanticValues = new HashMap<String, List<String>>();	// Reset semantic model in case of an exception
				uriToBlocks = new HashMap<String, List<Block>>();
				throw e;
			}
	}
	
	public void updateSemanticValues(Relation rel, ConcreteSpreadsheet spreadsheet) throws ModelException {
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
	
	public Message checkBlockForCompleteness(Block block, String uri, ConcreteSpreadsheet spreadsheet) throws ModelException {
		Message msg;
		
		if (!block.hasProperty(PropertyName.COMPLETESEMANTICBLOCK) ||
			block.getProperty(PropertyName.COMPLETESEMANTICBLOCK).equals("false") )
			msg = new Message(Message.MessageType.SemanticModelMsg, Message.MessageSubType.Info, "Unchecked block", block.getId());
		else if (!semanticValues.containsKey(uri)) 
			msg = new Message(Message.MessageType.SemanticModelMsg, Message.MessageSubType.Error, "No semantic information for block", block.getId());
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
			if (!semanticValues.get(uri).equals(values))
				msg =  new Message(Message.MessageType.SemanticModelMsg, Message.MessageSubType.SemanticIncomplete, "", block.getId());
			else
				msg =  new Message(Message.MessageType.SemanticModelMsg, Message.MessageSubType.Succeed, "", block.getId());
		} 
			
		return msg;
	}
	
	public List<Message> checkBlocksForCompleteness(List<Block> blocks, String uri, ConcreteSpreadsheet spreadsheet) throws ModelException {
		List<Message> messages = new ArrayList<Message>();
		
		for (Block b : blocks) {
			Message msg = checkBlockForCompleteness(b, uri, spreadsheet);
			if ((msg.getType() == Message.MessageType.SemanticModelMsg) && (msg.getSubType() != Message.MessageSubType.Succeed) )
				messages.add(msg);
		}
		
		if (messages.isEmpty() && !blocks.isEmpty())
			messages.add(new Message(Message.MessageType.SemanticModelMsg, Message.MessageSubType.Succeed, "", Util.convertBlocksToIDs(blocks)));
		
		return messages;
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
