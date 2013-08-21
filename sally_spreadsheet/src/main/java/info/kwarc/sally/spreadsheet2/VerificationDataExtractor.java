package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class VerificationDataExtractor {
	
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
	
	

}
