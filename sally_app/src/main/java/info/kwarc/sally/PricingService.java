package info.kwarc.sally;

import info.kwarc.sally.core.composition.SallyContext;
import info.kwarc.sally.core.composition.SallyInteraction;
import info.kwarc.sally.core.composition.SallyInteractionResultAcceptor;
import info.kwarc.sally.core.composition.SallyService;
import info.kwarc.sally.core.doc.DocumentInformation;
import info.kwarc.sally.core.doc.DocumentManager;
import info.kwarc.sally.core.interaction.SallyMenuItem;
import info.kwarc.sally.core.rdf.RDFStore;
import info.kwarc.sally.core.theo.Theo;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringWriter;
import java.util.Collection;
import java.util.HashSet;

import org.apache.commons.io.FilenameUtils;
import org.apache.commons.io.IOUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

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

@Singleton
public class PricingService {

	String pricingSparql;
	String navigateSparql;
	Model common;
	SallyInteraction sally;
	Logger log;
	ISallyWorkflowManager kb;
	DocumentManager docManager;
	RDFStore rdfStore;
	
	@Inject
	public PricingService(DocumentManager docManager, SallyInteraction sally, ISallyWorkflowManager kb, RDFStore rdfStore) {
		this.docManager = docManager; 
		pricingSparql = loadSparql("/pricing.sparql");
		navigateSparql = loadSparql("/navigate.sparql");
		this.rdfStore = rdfStore;
		
		this.sally = sally;
		this.kb = kb;
		log = LoggerFactory.getLogger(getClass());
	}

	private String loadSparql(String file) {
		try {
			InputStream is = getClass().getResourceAsStream(file);
			StringWriter writer = new StringWriter();
			IOUtils.copy(is, writer);
			return writer.toString();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return null;
	}

	@SallyService
	public void pricingService(final CADAlexClick uri, SallyInteractionResultAcceptor acceptor, final SallyContext context) {
		final Collection<String> files = getFiles(queryModel(uri.getCadNodeId()));
		if (files.size() ==0)
			return;
		

		for (final String file : files) {
			acceptor.acceptResult(new SallyMenuItem("Pricing", FilenameUtils.getName(file), "Open pricing information associated to the chosen CAD object") {
				@Override
				public void run() {
					Long parentProcessInstanceID = context.getContextVar("processInstanceId", Long.class);
					DocumentInformation docInfo = docManager.getDocumentInformation(file);
					Theo theo = docInfo.getTheo();
					kb.signal_global_event("switch_app", file);
					
					theo.openWindow(docInfo, parentProcessInstanceID, "Instance Selector", "http://localhost:8181/sally/pricing?node="+uri.getCadNodeId()+"&file="+file, 450, 600);
				}
			});
		}
	}

	public boolean isResultOk(QuerySolution sol) {
		String objthread = sol.get("objthread").asLiteral().getString();
		String threadVal = sol.get("threadval").asLiteral().getString();
		if (objthread.length()==0) {
			return true;
		}
		return threadVal.contains(objthread);
	}

	public Collection<String> getFiles(ResultSet results) {
		HashSet<String> result = new HashSet<String>();
		if (results == null)
			return result;

		while (results.hasNext()) {
			QuerySolution sol = results.next();
			if (!isResultOk(sol)) {
				continue;
			}
			result.add(sol.get("file").toString());
		}
		return result;
	}

	public ResultSet queryModel(String uri) {
		String queryStr = String.format(pricingSparql, uri);
		Query query = QueryFactory.create(queryStr);
		QueryExecution qe = QueryExecutionFactory.create(query, rdfStore.getModel());
		return qe.execSelect();		
	}
	
	public ResultSet getNavigate(String uri) {
		String queryStr = String.format(navigateSparql, uri, uri, uri, uri, uri, uri);
		Query query = QueryFactory.create(queryStr);
		QueryExecution qe = QueryExecutionFactory.create(query, rdfStore.getModel());
		return qe.execSelect();		
	}

}
