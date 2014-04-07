package info.kwarc.sally;

import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.networking.TemplateEngine;

import javax.ws.rs.GET;
import javax.ws.rs.Path;
import javax.ws.rs.QueryParam;

import org.slf4j.Logger;

import Sally.CADNavigateTo;

import com.google.inject.Inject;

@Path("sally/instance/navigate")
public class InstanceServiceNavigate {

	Logger log;
	PricingService pricingService;
	TemplateEngine te;
	ISallyWorkflowManager kb;

	@Inject
	public InstanceServiceNavigate(PricingService pricingService, TemplateEngine te, ISallyWorkflowManager kb) {
		this.pricingService = pricingService;
		this.te = te;
		log = org.slf4j.LoggerFactory.getLogger(getClass());
		this.kb = kb;
	}

	@GET
	public String get(@QueryParam("uri") String uri, @QueryParam("file") String file){
		CADNavigateTo.Builder request = CADNavigateTo.newBuilder();
		request.setCadNodeId(uri).setFileName(file).build();
		kb.signal_global_event("navigateTo", request.build());
		return "";
	}
}
