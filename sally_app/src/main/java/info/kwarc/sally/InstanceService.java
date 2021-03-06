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

import sally.MMTUri;

import com.google.inject.Inject;
import com.google.inject.Singleton;
import com.hp.hpl.jena.query.Query;
import com.hp.hpl.jena.query.QueryExecution;
import com.hp.hpl.jena.query.QueryExecutionFactory;
import com.hp.hpl.jena.query.QueryFactory;
import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ResultSet;

@Singleton
public class InstanceService {

	String instanceSparql;
	DocumentManager docManager;
	
	SallyInteraction sally;
	Logger log;
	ISallyWorkflowManager kb;
	RDFStore rdfStore;
	
	@Inject
	public InstanceService(DocumentManager docManager, SallyInteraction sally, ISallyWorkflowManager kb, RDFStore rdfStore) {
		this.docManager = docManager;
		instanceSparql = loadSparql("/instance.sparql");
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
	public void pricingService(final MMTUri uri, SallyInteractionResultAcceptor acceptor, final SallyContext context) {
		final Collection<String> files = getFiles(queryModel(uri.getUri()));
		if (files.size() ==0)
			return;

		for (final String file : files) {
			acceptor.acceptResult(new SallyMenuItem("CAD Objects", FilenameUtils.getName(file), "Open list of CAD objects corresponding to your selection") {
				@Override
				public void run() {
					Long parentProcessInstanceID = context.getContextVar("processInstanceId", Long.class);

					kb.signal_global_event("switch_app", file);
					String URL = "http://localhost:8181/sally/instance?node="+uri.getUri()+"&file="+file;
					log.info("opening "+URL);
					DocumentInformation docInfo = docManager.getDocumentInformation(file);
					Theo theo = docInfo.getTheo();
					//TODO Changed this temporarily to match with the processInstanceId argument
					theo.openWindow(docInfo, parentProcessInstanceID, "Pricing results", URL, 300, 600);
				}
			});
		}
	}

	public boolean isResultOk(QuerySolution sol) {
		return true;
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

		String queryStr = String.format(instanceSparql, uri);
		Query query = QueryFactory.create(queryStr);
		QueryExecution qe = QueryExecutionFactory.create(query, rdfStore.getModel());
		return qe.execSelect();		
	}
}
