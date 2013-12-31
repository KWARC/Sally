package info.kwarc.sally.core.rdf;

import java.util.HashMap;

import com.google.inject.Singleton;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;

@Singleton
public class RDFStore {

		Model model;
		HashMap<String, Model> models;
	
		public RDFStore() {
			models = new HashMap<String, Model>();
			model = ModelFactory.createDefaultModel();
		}
		
		private void recalcModel() {
			model = ModelFactory.createDefaultModel();
			for (Model m : models.values()) {
				model.add(m);
			}
		}
		
		public void addModel(String fileName, Model model) {
			models.put(fileName, model);
			recalcModel();
		}
		
		public Model getModel() {
			return model;
		}
}
