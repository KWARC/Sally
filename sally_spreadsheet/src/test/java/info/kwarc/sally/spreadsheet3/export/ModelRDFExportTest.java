package info.kwarc.sally.spreadsheet3.export;

import info.kwarc.sally.spreadsheet3.WinogradData;
import info.kwarc.sally.spreadsheet3.model.ModelManager;

import com.hp.hpl.jena.rdf.model.Model;

public class ModelRDFExportTest {
	public static void main(String[] args) {
		WinogradData data = new WinogradData();
		ModelManager manager = data.getModelManager();
		Model m = ModelRDFExport.getRDF(manager, "test.xml");
		m.write(System.out, "N3");
	}
}
