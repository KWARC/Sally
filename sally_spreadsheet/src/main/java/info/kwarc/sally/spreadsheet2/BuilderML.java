package info.kwarc.sally.spreadsheet2;

public abstract class BuilderML {
	
	abstract String getVIVaribale(int i);
	
	abstract String getIdentifier(String s);
	
	abstract String getMathTagBegin();
	
	abstract String getMathTagEnd();
	
	abstract String getOperatorApplication(String cd, String symbol);
	
	abstract String getApplicationEnd();

}
