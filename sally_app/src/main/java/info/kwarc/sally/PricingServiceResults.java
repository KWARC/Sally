package info.kwarc.sally;

import info.kwarc.sally.networking.TemplateEngine;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import javax.ws.rs.GET;
import javax.ws.rs.Path;
import javax.ws.rs.QueryParam;

import com.google.inject.Inject;
import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ResultSet;


@Path("sally/pricing")
public class PricingServiceResults {
	
	
	PricingService pricingService;
	TemplateEngine te;
	
	@Inject
	public PricingServiceResults(PricingService pricingService, TemplateEngine te ) {
		this.pricingService = pricingService;
		this.te = te;
	}
	
	@GET
	public String get(@QueryParam("node") String node){
		ResultSet results = pricingService.queryModel(node);
		HashMap<String, Object> objects = new HashMap<String, Object>();
		int sols = 0;
		List<QuerySolution> details = new ArrayList<QuerySolution>();
		while (results.hasNext()) {
			QuerySolution sol = results.next();
			sols++;
			details.add(sol);
		}
		objects.put("sols", Integer.toString(sols));
		objects.put("details", details);
		return te.generateTemplate("pricing/pricing.ftl", objects);
	}
}
