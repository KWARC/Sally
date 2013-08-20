package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

class MessageConverter {
	
	// ++ Converting: Message -> Objects ++
	
	public static CellSpaceInformation cellPositionToCellSpaceInformaiton(sally.CellPosition2 msg) {
		return new CellSpaceInformation(msg.getSheet(), msg.getRow(), msg.getCol());
	}
	
	public static List<CellSpaceInformation> cellPositionsToCellSpaceInformationList(sally.CellPositions2 msg) {
		List<CellSpaceInformation> posList = new ArrayList<CellSpaceInformation>();
		for (sally.CellPosition2 p : msg.getCellPositionsList()) 
			posList.add(cellPositionToCellSpaceInformaiton(p));
		return posList;
	}
	
	public static RangeInformation cellRangePositionToRangeInformation(sally.CellRangePosition2 msg) {
		return new RangeInformation(msg.getStartPos().getSheet(), 
				msg.getStartPos().getRow(), msg.getStartPos().getCol(),
				msg.getEndPos().getRow(), msg.getEndPos().getCol());
	}
	
	public static List<Integer> idListToIntegerList(sally.IDList msg) {
		List<Integer> intList = new ArrayList<Integer>();
		for (sally.IDMessage idMsg : msg.getIdListList())
			intList.add(idMsg.getId());
		return intList;
	}
	
	public static ValueInterpretation valueInterpretationMsgToObj(sally.ValueInterpretation msg) {
		Map<Integer, String> subExpressions = new HashMap<Integer, String>();
		for (sally.IntegerStringPair pair : msg.getSubExpressions().getPairList())
			subExpressions.put(pair.getId(), pair.getValue());
		return new ValueInterpretation(msg.getPatternString(), subExpressions, msg.getInterpretationTemplate());
	}
	
	// ++ Converting: Object -> Message ++
	
	public static sally.IDMessage integerToIDMessage(Integer integer) {
		return sally.IDMessage.newBuilder().setId(integer).build();
	}
	
	public static sally.IDList integerListToIDList(List<Integer> integerList) {
		sally.IDList.Builder idListBuilder = sally.IDList.newBuilder();
		for (Integer i : integerList) {
			idListBuilder.addIdList(integerToIDMessage(i));
		}
		return idListBuilder.build();
	}
	
	public static sally.CellPosition2 cellSpaceInformationToCellPosition(CellSpaceInformation cellSpaceInformation) {
		return sally.CellPosition2.newBuilder().setSheet(cellSpaceInformation.getWorksheet()).setRow(cellSpaceInformation.getRow()).setCol(cellSpaceInformation.getColumn()).build();
	}
	
	public static sally.CellPositions2 cellSpaceInformationListToCellPositions(List<CellSpaceInformation> cellSpaceInformationList) {
		sally.CellPositions2.Builder cellPositionsMsg = sally.CellPositions2.newBuilder();
		for (CellSpaceInformation position : cellSpaceInformationList)
			cellPositionsMsg.addCellPositions(cellSpaceInformationToCellPosition(position));
		return cellPositionsMsg.build();
	}
	
	public static sally.CellRangePosition2 RangeInformationToCellRangePosition(RangeInformation range) {
		return sally.CellRangePosition2.newBuilder().
			setStartPos(sally.CellPosition2.newBuilder().setSheet(range.getWorksheet()).setRow(range.getStartRow()).setCol(range.getStartCol()).build()).
			setEndPos(sally.CellPosition2.newBuilder().setSheet(range.getWorksheet()).setRow(range.getEndRow()).setCol(range.getEndCol()).build()).build();
	}

}
