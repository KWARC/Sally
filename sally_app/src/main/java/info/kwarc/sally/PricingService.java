package info.kwarc.sally;

import info.kwarc.sally.core.SallyContext;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.SallyService;
import info.kwarc.sally.core.comm.SallyMenuItem;
import info.kwarc.sally.core.comm.SallyModelRequest;
import info.kwarc.sally.core.interfaces.Theo;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.commons.io.IOUtils;

import sally.CADAlexClick;

import com.google.inject.Inject;
import com.google.inject.Singleton;
import com.hp.hpl.jena.query.Query;
import com.hp.hpl.jena.query.QueryExecution;
import com.hp.hpl.jena.query.QueryExecutionFactory;
import com.hp.hpl.jena.query.QueryFactory;
import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ResultSet;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;

@Singleton
public class PricingService {

	String pricingSparql;
	Model common;
	Theo theo;
	SallyInteraction sally;
	
	@Inject
	public PricingService(Theo theo, SallyInteraction sally) {
		this.theo = theo;
		loadPricingSparql();
		common = null;
		this.sally = sally;
	}
	
	private void loadModels() {
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
	public void pricingService(final CADAlexClick uri, SallyInteractionResultAcceptor acceptor, SallyContext context) {
		final ResultSet cellURI = queryModel(uri.getCadNodeId());
		if (cellURI == null || !cellURI.hasNext())
			return;
		
		acceptor.acceptResult(new SallyMenuItem("Pricing", "Open pricing.xls") {
			@Override
			public void run() {
				theo.openWindow("Pricing results", "http://localhost:8181/sally/pricing?node="+uri.getCadNodeId(), 300, 600);
			}
		});
	}
	
	public ResultSet queryModel(String uri) {
		if (common == null)
			loadModels();
		if (common == null) {
			return null;
		}
		
		String queryStr = String.format(pricingSparql, uri);
		Query query = QueryFactory.create(queryStr);
		QueryExecution qe = QueryExecutionFactory.create(query, common);
		return qe.execSelect();		
	}
}
