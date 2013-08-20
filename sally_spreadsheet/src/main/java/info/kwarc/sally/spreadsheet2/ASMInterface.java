package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.List;

public class ASMInterface {
	
	Manager manager;
	
	public ASMInterface() {
		manager = new Manager();
	}
	
	// ++ Parsing of messages that are related to blocks ++
	
	public void createBlockRange(sally.CreateBlockRange msg) {
		manager.createComposedBlock( Util.expandRange( MessageConverter.cellPositionToCellSpaceInformaiton( msg.getRange().getStartPos()),
				MessageConverter.cellPositionToCellSpaceInformaiton(msg.getRange().getEndPos())) );		
	}
	
	public void createBlock(sally.CreateBlock msg) {
		manager.createComposedBlock(MessageConverter.cellPositionsToCellSpaceInformationList(msg.getCells()));
	}
	
	public void createComposedBlock(sally.CreateComposedBlock msg) {
		manager.createBlock(Util.convertIDsToBlocks(msg.getBlockIdsList(), manager));
	}
	
	public sally.IDList getBlocksForPosition(sally.GetBlocksForPosition msg) {
		return MessageConverter.integerListToIDList(Util.convertBlocksToIDs( manager.getBlocksForPosition(MessageConverter.cellPositionToCellSpaceInformaiton(msg.getPosition())) ));
	}
	
	public sally.IDList getBlocksInRange(sally.GetBlocksInRange msg) {
		return MessageConverter.integerListToIDList(Util.convertBlocksToIDs( manager.getBlocksInRange(MessageConverter.cellRangePositionToRangeInformation(msg.getRange()))));
	}
	
	public sally.CellPositions2 getAllPositionsOfBlock(sally.GetAllPositionsOfBlock msg) {
		return MessageConverter.cellSpaceInformationListToCellPositions(manager.getBlockByID(msg.getId().getId()).getCells());
	}
	
	public sally.IDList getSubBlocks(sally.GetSubBlock msg) {
		return MessageConverter.integerListToIDList(Util.convertBlocksToIDs(manager.getBlockByID(msg.getId().getId()).getSubBlocks()));
	}
	
	// ++ Parsing of messages that are related to relations ++
	
	public void createFunctionalRelation(sally.CreateFunctionalRelation msg) {
		manager.createFunctionalRelation(Util.convertIDsToBlocks(MessageConverter.idListToIntegerList(msg.getBlockIds()), manager), "");   // TODO: Function ?
	}
	
	public sally.IDList getRelationsForPosition(sally.GetRelationsForPosition msg) {
		return MessageConverter.integerListToIDList(Util.convertRelationsToIDs( manager.getRelationForPosition(MessageConverter.cellPositionToCellSpaceInformaiton(msg.getPosition()) )));
	}
	
	public sally.CellPositionsList2 getCellRelationsForPosition(sally.GetCellRelationsForPosition msg) {
		List<CellTuple> tupleList;
		if (!msg.hasRelationId()) {
			tupleList = manager.getCellRelationsForPosition(MessageConverter.cellPositionToCellSpaceInformaiton(msg.getPosition()));
		} else {
			tupleList = manager.getCellRelationsForPosition(MessageConverter.cellPositionToCellSpaceInformaiton(msg.getPosition()), manager.getRelationByID(msg.getRelationId().getId()));
		}
		sally.CellPositionsList2.Builder tupleListMsg = sally.CellPositionsList2.newBuilder();
		for (CellTuple tuple : tupleList)
			tupleListMsg.addCellPositionsList(MessageConverter.cellSpaceInformationListToCellPositions(tuple.getTuple()));
		return tupleListMsg.build();
	}
	
	// ++ Parsing of messages that are related to ontology links ++
	
	public void createOntologyBlockLink(sally.CreateOntologyBlockLink msg) {
		List<ValueInterpretation> valueInterpretations = new ArrayList<ValueInterpretation>();
		for (sally.ValueInterpretation vi : msg.getValueInterpretationsList())
			valueInterpretations.add(MessageConverter.valueInterpretationMsgToObj(vi));
		manager.getBlockByID(msg.getBlockId()).setOntologyLink(new OntologyBlockLink(msg.getUri(), valueInterpretations));
	}
	
	public void createOntologyRelationLink(sally.CreateOntologyRelationLink msg) {
		manager.getRelationByID(msg.getId()).setOntologyLink(new OntologyRelationLink(msg.getUri(), msg.getMathMLTemplate(),
				Util.convertBlocksToOntologyLinks(Util.convertIDsToBlocks(MessageConverter.idListToIntegerList(msg.getBlockIds()), manager))));
	}
	
	public sally.StringMessage getUriForBlock(sally.GetUriForBlock msg) {
		return sally.StringMessage.newBuilder().setData(manager.getBlockByID(msg.getBlockID().getId()).getOntologyLink().getUri()).build();
	}
	
	public sally.StringMessage getValueInterpretation(sally.GetValueInterpretation msg) {
		return sally.StringMessage.newBuilder().setData(manager.getBlockByID(msg.getBlockID().getId()).getOntologyLink().getValueInterpretation(msg.getValue()) ).build();
	}
	
	public sally.StringMessage getUriForRelation(sally.GetUriForRelation msg) {
		return sally.StringMessage.newBuilder().setData(manager.getRelationByID(msg.getRelationID().getId()).getOntologyLink().getUri() ).build();
	}
	
	public sally.StringMessage getIntendedFunctionForValues(sally.GetIntendedFunctionForValues msg) {
		return sally.StringMessage.newBuilder().setData(manager.getRelationByID(msg.getRelationID().getId()).getOntologyLink().getRelationInterpretation(msg.getValuesList())).build();
	}
	

}
