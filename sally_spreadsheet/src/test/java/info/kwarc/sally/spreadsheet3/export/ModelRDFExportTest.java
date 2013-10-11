package info.kwarc.sally.spreadsheet3.export;

import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.Manager;

import com.hp.hpl.jena.rdf.model.Model;

public class ModelRDFExportTest {
	public static void main(String[] args) {
		WinogradData data = new WinogradData();
		Manager manager = data.getManager();
		Model m = ModelRDFExport.getRDF(manager, "test.xml");
		m.write(System.out, "N3");
	}
}
