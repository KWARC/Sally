package info.kwarc.sally.html.pages;

import info.kwarc.sally.core.interaction.CallbackManager;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.networking.TemplateEngine;

import javax.ws.rs.GET;
import javax.ws.rs.Path;
import javax.ws.rs.QueryParam;

import org.slf4j.Logger;

import sally.HTMLSelectPart;

import com.google.inject.Inject;

@Path("sally/html/navigateTo")
public class HTMLNavigateToPage {

	Logger log;
	TemplateEngine te;
	ISallyWorkflowManager kb;
	CallbackManager callbacks;
	
	@Inject
	public HTMLNavigateToPage(TemplateEngine te, ISallyWorkflowManager kb, CallbackManager callbacks) {
		this.te = te;
		log = org.slf4j.LoggerFactory.getLogger(getClass());
		this.kb = kb;
		this.callbacks= callbacks;
	}

	@GET
	public String get(@QueryParam("id") String id, @QueryParam("callbackid") Long callbackid){
		this.callbacks.getCallback(callbackid).onMessage(HTMLSelectPart.newBuilder().setId(id).buildPartial());
		return "";
	}
}
