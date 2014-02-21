package info.kwarc.sally.spreadsheet3.extraction;

import java.util.ArrayList;
import java.util.List;

/**
 * This class tries to find relations between areas (blocks).
 * @author cliguda
 *
 */
public class AffiliationInformationExtraction {
	
	public static List<AffiliationInformation> extract(AEResults aeResults) {
		List<AffiliationInformation> results = new ArrayList<AffiliationInformation>();
		
		List<AreaInformation> areas = aeResults.getAreas();
		for (AreaInformation area : areas) {
			List<Integer> legendIds = new ArrayList<Integer>();
			
			if (area.getType() == StructureType.LEGENDHEADER) {	
				for (AreaInformation a : areas) {
					
					if ((a.getType() == StructureType.LEGEND) && (a.getDistanceFrom(area.getRanges().get(0).getStartPosition()) == 1) && (area.isAbove(a) || area.isLeftFrom(a) ) )
						legendIds.add(a.getId());
				}
			} else if (area.getType() == StructureType.FB) {
				// Go to the top
				int row = area.getStartRow();
				boolean goTop = (row > 0);
				while (goTop) {
					row--;
					for (int column = area.getStartColumn(); column <= area.getEndColumn(); column++) {
						if ((aeResults.getRep(row, column).getType() == StructureType.LEGEND) || ((aeResults.getRep(row, column).getType() == StructureType.LEGENDHEADER) && legendIds.isEmpty()) ) {
							for (Integer id : aeResults.getRep(row, column).getIndices())
								if (!legendIds.contains(id))
									legendIds.add(id);
						} else if (aeResults.getRep(row, column).getType() == StructureType.FB) {
							if (!legendIds.isEmpty())
								goTop = false;
						}
					}
					goTop = (goTop && (row > 0));
				}
				
				// Go to the left
				List<Integer> legendIdsLeft = new ArrayList<Integer>();
				int column = area.getStartColumn();
				boolean goLeft = (column > 0);
				while (goLeft) {
					column--;
					for ( row = area.getStartRow(); row <= area.getEndRow(); row++) {
						if ((aeResults.getRep(row, column).getType() == StructureType.LEGEND) || ((aeResults.getRep(row, column).getType() == StructureType.LEGENDHEADER) && legendIdsLeft.isEmpty()) ) {
							for (Integer id : aeResults.getRep(row, column).getIndices())
								if (!legendIdsLeft.contains(id))
									legendIdsLeft.add(id);
						} else if (aeResults.getRep(row, column).getType() == StructureType.FB) {
							if (!legendIdsLeft.isEmpty())
								goLeft = false;
						}
					}
					goLeft = (goLeft && (column > 0));
				}
				legendIds.addAll(legendIdsLeft);
			}
			
			if (!legendIds.isEmpty())
				results.add(new AffiliationInformation(area.getId(), legendIds));
		}
		
		return results;
	}

}
