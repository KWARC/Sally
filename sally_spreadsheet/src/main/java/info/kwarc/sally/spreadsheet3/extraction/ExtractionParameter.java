package info.kwarc.sally.spreadsheet3.extraction;

public class ExtractionParameter {
	private boolean textAsLegend, formulaAsFB, doubleAsFB, colorAsStructure, borderAsStructure, fontAsStructure, createAmbiguousInformation;

	public ExtractionParameter(boolean textAsLegend, boolean colorAsStructure,
			boolean borderAsStructure, boolean fontAsStructure) {
		super();
		this.textAsLegend = textAsLegend;
		this.colorAsStructure = colorAsStructure;
		this.borderAsStructure = borderAsStructure;
		this.fontAsStructure = fontAsStructure;
		
		//Should also be parameterized
		formulaAsFB = true;
		doubleAsFB = true;
		createAmbiguousInformation = true;
	}

	public boolean isTextAsLegend() {
		return textAsLegend;
	}

	public boolean isColorAsStructure() {
		return colorAsStructure;
	}

	public boolean isBorderAsStructure() {
		return borderAsStructure;
	}

	public boolean isFontAsStructure() {
		return fontAsStructure;
	}

	public boolean isFormulaAsFB() {
		return formulaAsFB;
	}

	public boolean isDoubleAsFB() {
		return doubleAsFB;
	}
	
	public boolean iscreateAmbiguousInformation() {
		return createAmbiguousInformation;
	}
	
}
