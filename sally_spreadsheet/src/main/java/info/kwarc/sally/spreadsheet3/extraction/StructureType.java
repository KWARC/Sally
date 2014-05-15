package info.kwarc.sally.spreadsheet3.extraction;

public enum StructureType {
	EMPTY, FB, LEGEND, LEGENDHEADER, UNKNOWN, HIDDEN;
	
	public static final StructureType[] cellTypeValues = StructureType.values();
}