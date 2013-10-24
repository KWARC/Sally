package info.kwarc.sally;

import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.networking.TemplateEngine;

import javax.ws.rs.GET;
import javax.ws.rs.Path;
import javax.ws.rs.QueryParam;

import org.slf4j.Logger;

import sally.AlexRangeRequest;
import sally.RangeSelection;

import com.google.inject.Inject;
import com.hp.hpl.jena.query.QuerySolution;
import com.hp.hpl.jena.query.ResultSet;

@Path("sally/pricing/navigate")
public class PricingServiceNavigate {

	Logger log;
	PricingService pricingService;
	TemplateEngine te;
	ISallyWorkflowManager kb;

	@Inject
	public PricingServiceNavigate(PricingService pricingService, TemplateEngine te, ISallyWorkflowManager kb) {
		this.pricingService = pricingService;
		this.te = te;
		log = org.slf4j.LoggerFactory.getLogger(getClass());
		this.kb = kb;
	}

	@GET
	public String get(@QueryParam("uri") String uri){
		ResultSet resultSet = pricingService.getNavigate(uri);
		AlexRangeRequest.Builder request = AlexRangeRequest.newBuilder();
		while (resultSet.hasNext()) {
			QuerySolution sol = resultSet.next();
			request.setFileName(sol.get("file").toString());
			RangeSelection sel = RangeSelection.newBuilder().setSheet(sol.get("sheet").toString())
											.setStartRow(sol.get("startrow").asLiteral().getInt())
											.setStartCol(sol.get("startcol").asLiteral().getInt())
											.setEndRow(sol.get("endrow").asLiteral().getInt())
											.setEndCol(sol.get("endcol").asLiteral().getInt()).build();
			request.addSelection(sel);
		}
		kb.signal_global_event("navigateTo", request.build());
		return "";
	}
}
