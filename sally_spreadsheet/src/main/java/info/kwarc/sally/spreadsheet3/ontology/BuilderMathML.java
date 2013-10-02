package info.kwarc.sally.spreadsheet3.ontology;

public class BuilderMathML extends BuilderML {
	
	@Override
	public String getVIVaribale(int i) {
		return "<rvar num=\"" + i + "\"/>";
	}

	@Override
	public String getIdentifier(String s) {
		return "<ci>" + s + "</ci>";
	}

	@Override
	public String getMathTagBegin() {
		return "<math xmlns=\"http://www.w3.org/1998/Math/MathML\">";
	}
	
	@Override
	public String getMathTagEnd() {
		return "</math>";
	}
	
	@Override
	public String getOperatorApplication(String cd, String symbol) {
		return "<apply>\n<csymbol cd=\"" + cd + "\">" + symbol + "</csymbol>";
	}

	@Override
	public String getApplicationEnd() {
		return "</apply>";
	}

}
