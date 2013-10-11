package info.kwarc.sally.tasks;

import info.kwarc.sally.ProcessDocMappings;
import info.kwarc.sally.core.SallyInteraction;
import info.kwarc.sally.core.interfaces.SallyTask;
import info.kwarc.sally.networking.interfaces.INetworkSender;
import info.kwarc.sally.spreadsheet.interfaces.WorksheetFactory;
import info.kwarc.sissi.bpm.inferfaces.ISallyKnowledgeBase;
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
import sally.SpreadsheetAlexData;
import sally.WhoAmI;
import sally.WhoAmI.DocType;

import com.google.inject.Inject;

@SallyTask(action="CreateDoc")
public class CreateDoc implements WorkItemHandler {

	CADFactory cadFactory;
	WorksheetFactory spreadsheetFactory;
	SallyInteraction interaction;
	ISallyKnowledgeBase kb;
	ProcessDocMappings docMap;
	Logger log;

	@Inject
	public CreateDoc(CADFactory cadFactory, WorksheetFactory spreadsheetFactory, SallyInteraction interaction, ISallyKnowledgeBase kb, ProcessDocMappings docMap) {
		this.cadFactory = cadFactory;
		this.spreadsheetFactory = spreadsheetFactory;
		this.interaction = interaction;
		this.kb = kb;
		this.docMap = docMap;
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
		
		Map<String, Object> variable = HandlerUtils.getProcessVariables(kb.getProcessInstance(workItem.getProcessInstanceId()));
		INetworkSender networkSender = HandlerUtils.safeGet(variable, "NetworkSender", INetworkSender.class);		
		try{
			if (networkSender == null)
				throw new Exception("No network sender available.");
				
			if (alexInfo == null)
				throw new Exception("No WhoAmI object passed to document creation. Aborting document creation.");
			if (alexData == null)
				throw new Exception("No AlexData object passed to document creation. Aborting document creation.");

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

			if (processId == null || processInput == null) {
				throw new Exception("Could not handle document type "+alexInfo.getDocumentType());
			}

			interaction.registerServices(processInput);
			// AbstractSpreadsheetInput

			ProcessInstance instance = kb.startProcess(workItem.getProcessInstanceId(), processId, params);
			
			docMap.addMap(workItem.getProcessInstanceId(), alexData.getFileName(), instance.getId());
		} catch (Exception e) {
			log.error(e.getMessage());
		} finally {
			manager.completeWorkItem(workItem.getId(), null);
		}
	}
}
