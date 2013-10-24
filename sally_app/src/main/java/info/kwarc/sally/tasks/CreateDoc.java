package info.kwarc.sally.tasks;

import info.kwarc.sally.core.DocumentInformation;
import info.kwarc.sally.core.DocumentManager;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.core.net.INetworkSender;
import info.kwarc.sally.core.theo.Theo;
import info.kwarc.sally.core.workflow.ISallyWorkflowManager;
import info.kwarc.sally.html.HTMLFactory;
import info.kwarc.sally.sketch.SketchFactory;
import info.kwarc.sally.spreadsheet.interfaces.WorksheetFactory;
import info.kwarc.sissi.bpm.tasks.HandlerUtils;
import info.kwarc.sissi.model.document.cad.interfaces.CADFactory;

import java.util.HashMap;
import java.util.Map;

import org.apache.commons.codec.binary.Base64;
import org.drools.process.instance.WorkItemHandler;
import org.drools.runtime.process.ProcessInstance;
import org.drools.runtime.process.WorkItem;
import org.drools.runtime.process.WorkItemManager;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.AlexData;
import sally.CADSemanticData;
import sally.HTMLASM;
import sally.SketchASM;
import sally.SpreadsheetAlexData;
import sally.WhoAmI;
import sally.WhoAmI.DocType;

import com.github.jucovschi.ProtoCometD.ProtoUtils;
import com.google.inject.Inject;
import com.google.protobuf.AbstractMessage;

@SallyTask(action="CreateDoc")
public class CreateDoc implements WorkItemHandler {

	CADFactory cadFactory;
	WorksheetFactory spreadsheetFactory;
	SketchFactory sketchFactory;
	HTMLFactory htmlFactory;

	SallyInteraction interaction;
	ISallyWorkflowManager kb;
	DocumentManager docManager;
	Logger log;

	@Inject
	public CreateDoc(CADFactory cadFactory, WorksheetFactory spreadsheetFactory, SketchFactory sketchFactory, HTMLFactory htmlFactory, SallyInteraction interaction, ISallyWorkflowManager kb, DocumentManager docMap) {
		this.cadFactory = cadFactory;
		this.spreadsheetFactory = spreadsheetFactory;
		this.sketchFactory = sketchFactory;
		this.htmlFactory = htmlFactory;
		this.interaction = interaction;
		this.kb = kb;
		this.docManager = docMap;
		this.log = LoggerFactory.getLogger(this.getClass());
	}

	@Override
	public void abortWorkItem(WorkItem workItem, WorkItemManager manager) {
		manager.completeWorkItem(workItem.getId(), null);
	}
	@Override
	public void executeWorkItem(WorkItem workItem, WorkItemManager manager) {
		WhoAmI alexInfo = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), WhoAmI.class);
		AlexData alexData = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), AlexData.class);
		Theo theo = HandlerUtils.getFirstTypedParameter(workItem.getParameters(), Theo.class);;
		
		Map<String, Object> variable = HandlerUtils.getProcessVariables(kb.getProcessInstance(workItem.getProcessInstanceId()));
		INetworkSender networkSender = HandlerUtils.safeGet(variable, "NetworkSender", INetworkSender.class);		
		try{
			if (networkSender == null)
				throw new Exception("No network sender available.");
				
			if (alexInfo == null)
				throw new Exception("No WhoAmI object passed to document creation. Aborting document creation.");
			if (alexData == null)
				throw new Exception("No AlexData object passed to document creation. Aborting document creation.");
			if (theo== null)
				throw new Exception("No Theo object passed to document creation. Aborting document creation.");

			byte[] res = Base64.decodeBase64(alexData.getData());
			String processId = null;
			Object processInput = null;
			Map<String, Object> params = new HashMap<String, Object>();

			if (alexInfo.getDocumentType() == DocType.Spreadsheet) {
				SpreadsheetAlexData rr ;
				try {
					rr = SpreadsheetAlexData.parseFrom(res);
				} catch (Exception e) {
					rr = SpreadsheetAlexData.newBuilder().build();
				}
				processInput = spreadsheetFactory.create(alexData.getFileName(), rr, networkSender);
				params.put("ASMInput", processInput);
				processId = "Sally.spreadsheet";
			}
			if (alexInfo.getDocumentType() == DocType.CAD) {
				CADSemanticData rr = CADSemanticData.parseFrom(res);
				processInput = cadFactory.create(alexData.getFileName(), rr, networkSender);
				params.put("CSMInput", processInput);
				processId = "Sally.cad";
			}
			if (alexInfo.getDocumentType() == DocType.Sketch) {
				//log.info(msg);
				AbstractMessage msg = ProtoUtils.deserialize(alexData.getData());
				if (msg instanceof SketchASM) {
					SketchASM sketchASM = (SketchASM) msg;
					processInput = sketchFactory.create(alexData.getFileName(), sketchASM, networkSender);					
					processId = "Sally.sketch";
				} else if (msg instanceof HTMLASM) {
					HTMLASM htmlASM = (HTMLASM) msg;
					processInput = htmlFactory.create(alexData.getFileName(), htmlASM, networkSender);					
					processId = "Sally.html";
				} else
					throw new Exception("Could not create document type "+msg.getClass());
				params.put("ASMInput", processInput);
			}

			if (processId == null || processInput == null) {
				throw new Exception("Could not handle document type "+alexInfo.getDocumentType());
			}

			interaction.registerServices(processInput);

			ProcessInstance instance = kb.startProcess(workItem.getProcessInstanceId(), processId, params);
			DocumentInformation docInfo = new DocumentInformation(alexData.getFileName(), instance.getId());
			docInfo.setTheo(theo);
			docInfo.setDocumentModel(processInput);
			docInfo.setNetworkSender(networkSender);
			docManager.addDocument(docInfo);
		} catch (Exception e) {
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem.getId(), null);
		}
	}
}
