package info.kwarc.sally.spreadsheet3.extraction;

public class ExtractionParameter {
	private boolean textAsLegend, formulaAsFB, doubleAsFB, colorAsStructure, borderAsStructure, fontAsStructure, createAmbiguousInformation;

	public ExtractionParameter(boolean textAsLegend, boolean formulaAsFB, boolean doubleAsFB, boolean colorAsStructure,
			boolean borderAsStructure, boolean fontAsStructure) {
		super();
		// Parameters for heuristic preprocessing
		this.textAsLegend = textAsLegend;
		this.formulaAsFB = formulaAsFB;
		this.doubleAsFB = doubleAsFB;
		
		// Parameters for area detection
		this.colorAsStructure = colorAsStructure;
		this.borderAsStructure = borderAsStructure;
		this.fontAsStructure = fontAsStructure;
		
		//Should also be parameterized
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
