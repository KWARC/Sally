package info.kwarc.sally;

import info.kwarc.sally.core.SallyActionAcceptor;
import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.comm.SallyModelRequest;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.commons.io.IOUtils;

import sally.MMTUri;

import com.hp.hpl.jena.query.Query;
import com.hp.hpl.jena.query.QueryExecution;
import com.hp.hpl.jena.query.QueryExecutionFactory;
import com.hp.hpl.jena.query.QueryFactory;
import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;

public class PricingService {

	String pricingSparql;
	Model common;
	
	public PricingService() {
		loadPricingSparql();
		common = null;
	}
	
	private void loadModels(SallyInteraction sally) {
		common = ModelFactory.createDefaultModel();
		List<Model> models = sally.getPossibleInteractions("/get/semantics", new SallyModelRequest(), Model.class);
		for (Model mod : models) {
			common.add(mod);
		}
	}
	
	private void loadPricingSparql() {
		try {
			InputStream is = getClass().getResourceAsStream("/pricing.sparql");
			StringWriter writer = new StringWriter();
			IOUtils.copy(is, writer);
			pricingSparql = writer.toString();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	@SallyService
	public void pricingService(MMTUri uri, SallyActionAcceptor acceptor, SallyContext context) {
		SallyInteraction sally = context.getCurrentInteraction();
		
		if (common == null)
			loadModels(sally);
		if (common == null) {
			return;
		}
		final String cellURI = queryModel(common, uri);
		if (cellURI == null)
			return;
		
		acceptor.acceptResult(new SallyMenuItem("Pricing", "Open blah.xls") {
			@Override
			public void run() {
				System.out.println("Navigate to " +cellURI);
			}
		});
	}
	
	public String queryModel(Model model, MMTUri uri) {
		Query query = QueryFactory.create(pricingSparql);
		QueryExecution qe = QueryExecutionFactory.create(query, model);
		ResultSet results = qe.execSelect();
		Map<String, Integer> cnt = new HashMap<String, Integer>();
		int cntMax = -1;
		String fbiMax = "";
		
		while (results.hasNext()) {
			QuerySolution sol = results.next();
			String fbi = sol.get("fbi").asResource().toString();
			if (!cnt.containsKey(fbi))
				cnt.put(fbi, 0);
			cnt.put(fbi, cnt.get(fbi) + 1);
			if (cnt.get(fbi) > cntMax) {
				cntMax = cnt.get(fbi);
				fbiMax = fbi;
			}
		}
		if (cntMax != -1)
			return fbiMax;
		else 
			return null;
	}
}
