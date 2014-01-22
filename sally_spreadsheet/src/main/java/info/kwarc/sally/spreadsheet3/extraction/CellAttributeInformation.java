package info.kwarc.sally.spreadsheet3.extraction;

import info.kwarc.sally.spreadsheet3.ContentValueType;


public class CellAttributeInformation {
	final static int vectorSize = 7;
	
	Boolean leftBorder, upperBorder, surroundingLegends, isBold, isItalic, isUnderlined;
	StructureType typeLeft, typeTop;
	ContentValueType contentType; 
	StructureType cellType = StructureType.UNKNOWN;
	
	public CellAttributeInformation(Boolean leftBorder, Boolean upperBorder,
			Boolean surroundingLegends, Boolean isBold,
			Boolean isItalic, Boolean isUnderlined, StructureType typeLeft,
			StructureType typeTop, ContentValueType contentType) {
		super();
		this.leftBorder = leftBorder;
		this.upperBorder = upperBorder;
		this.surroundingLegends = surroundingLegends;
		this.isBold = isBold;
		this.isItalic = isItalic;
		this.isUnderlined = isUnderlined;
		this.typeLeft = typeLeft;
		this.typeTop = typeTop;
		this.contentType = contentType;
	}
	
	/**
	 *  This constructor can be used if the structure type is already known. The additional information are needed for some
	 *  post processing operations.
	 */
	public CellAttributeInformation(StructureType type, Boolean leftBorder, Boolean upperBorder,
			Boolean isBold, Boolean isItalic, Boolean isUnderlined, ContentValueType contentType) {
		this.cellType = type;
		this.leftBorder = leftBorder;
		this.upperBorder = upperBorder;
		this.isBold = isBold;
		this.isItalic = isItalic;
		this.isUnderlined = isUnderlined;
		this.contentType = contentType;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((contentType == null) ? 0 : contentType.hashCode());
		result = prime * result + ((isBold == null) ? 0 : isBold.hashCode());
		result = prime * result
				+ ((isItalic == null) ? 0 : isItalic.hashCode());
		result = prime * result
				+ ((isUnderlined == null) ? 0 : isUnderlined.hashCode());
		result = prime * result
				+ ((leftBorder == null) ? 0 : leftBorder.hashCode());
		result = prime
				* result
				+ ((surroundingLegends == null) ? 0 : surroundingLegends
						.hashCode());
		result = prime * result
				+ ((typeLeft == null) ? 0 : typeLeft.hashCode());
		result = prime * result + ((typeTop == null) ? 0 : typeTop.hashCode());
		result = prime * result
				+ ((upperBorder == null) ? 0 : upperBorder.hashCode());
		return result;
	}
	

	// WARNING: cell type is not part of the comparison
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		CellAttributeInformation other = (CellAttributeInformation) obj;
		if (contentType != other.contentType)
			return false;
		if (isBold == null) {
			if (other.isBold != null)
				return false;
		} else if (!isBold.equals(other.isBold))
			return false;
		if (isItalic == null) {
			if (other.isItalic != null)
				return false;
		} else if (!isItalic.equals(other.isItalic))
			return false;
		if (isUnderlined == null) {
			if (other.isUnderlined != null)
				return false;
		} else if (!isUnderlined.equals(other.isUnderlined))
			return false;
		if (leftBorder == null) {
			if (other.leftBorder != null)
				return false;
		} else if (!leftBorder.equals(other.leftBorder))
			return false;
		if (surroundingLegends == null) {
			if (other.surroundingLegends != null)
				return false;
		} else if (!surroundingLegends.equals(other.surroundingLegends))
			return false;
		if (typeLeft != other.typeLeft)
			return false;
		if (typeTop != other.typeTop)
			return false;
		if (upperBorder == null) {
			if (other.upperBorder != null)
				return false;
		} else if (!upperBorder.equals(other.upperBorder))
			return false;
		return true;
	}
	
	public StructureType getCellType() {
		return cellType;
	}

	public void setCellType(StructureType cellType) {
		this.cellType = cellType;
	}
	
	public static String getHeader() {
		return "Type," + getAttributeHeader();
	}
	
	public static String getAttributeHeader() {
		return "isLeftBorder,isUpperBorder,hasSurroundingLegends,hasConspicuousFont,leftType,topType,contentType";
	}
	
	public static String[] getAttributes() {
		return getAttributeHeader().split(",");
	}
	
	public void print() {
		String[] attr = getAttributes();
		Float[] rep = getNumberRepresentation();
		for (int i = 0; i < attr.length; i++)
			System.out.print(attr[i] + ": " + rep[i] + "  ");
		System.out.println(" -> " + getCellType().name());
	}
	
	public static int getVectorSize() {
		return vectorSize;
	}
	
	public Float[] getNumberRepresentation() {
		Float[] nodes = new Float[vectorSize];
		nodes[0] = leftBorder ? 1.0f : 0.0f;
		nodes[1] = upperBorder ? 1.0f : 0.0f;
		nodes[2] = surroundingLegends ? 1.0f : 0.0f;
		nodes[3] = (isBold || isItalic || isUnderlined) ? 1.0f :0.0f;
		nodes[4] = new Float(typeLeft.ordinal());
		nodes[5] = new Float(typeTop.ordinal());
		nodes[6] = new Float(contentType.ordinal());
		return nodes;
	}
	
	public void setSurroundingLegends(Boolean surroundingLegends) {
		this.surroundingLegends = surroundingLegends;
	}

	public void setTypeLeft(StructureType typeLeft) {
		this.typeLeft = typeLeft;
	}

	public void setTypeTop(StructureType typeTop) {
		this.typeTop = typeTop;
	}
	
	/*public Float[] getRapidRepresentation() {
		Float[] representation = new Float[vectorSize];
		representation[0] = leftBorder ? 1.0f : 0.0f;
		representation[1] = upperBorder ? 1.0f : 0.0f;
		representation[2] = surroundingLegends ? 1.0f : 0.0f;
		representation[3] = isBold ? 1.0f : 0.0f;
		representation[4] = isItalic ? 1.0f : 0.0f;
		representation[5] = isUnderlined ? 1.0f : 0.0f;
		representation[6] = new Float(typeLeft.ordinal());
		representation[7] = new Float(typeTop.ordinal());
		representation[8] = new Float(contentType.ordinal());
		return representation;
	}
	
	private svm_node createSVMNode(int index, double value) {
		svm_node node = new svm_node();
		node.index = index;
		node.value = value;
		return node;
	}*/
	
}
