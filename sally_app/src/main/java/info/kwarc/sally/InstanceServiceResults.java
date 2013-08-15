package info.kwarc.sally;

import info.kwarc.sally.networking.TemplateEngine;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import javax.ws.rs.GET;
import javax.ws.rs.Path;
import javax.ws.rs.QueryParam;

import org.slf4j.Logger;

import com.google.inject.Inject;
import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ResultSet;

@Path("sally/instance")
public class InstanceServiceResults {

	Logger log;
	InstanceService instanceService;
	TemplateEngine te;

	@Inject
	public InstanceServiceResults(InstanceService instanceService, TemplateEngine te ) {
		this.instanceService = instanceService;
		this.te = te;
		log = org.slf4j.LoggerFactory.getLogger(getClass());
	}

	@GET
	public String get(@QueryParam("node") String node, @QueryParam("file") String file){
		log.warn(file);
		ResultSet results = instanceService.queryModel(node);
		HashMap<String, Object> objects = new HashMap<String, Object>();
		List<QuerySolution> details = new ArrayList<QuerySolution>();
		while (results.hasNext()) {
			QuerySolution sol = results.next();
			if (!sol.get("file").toString().equals(file)) {
				continue;
			}
			if (!instanceService.isResultOk(sol)) {
				continue;
			}
			details.add(sol);
		}
		objects.put("node", node);
		objects.put("solutions", details);
		return te.generateTemplate("instance/instance.ftl", objects);
	}
}
