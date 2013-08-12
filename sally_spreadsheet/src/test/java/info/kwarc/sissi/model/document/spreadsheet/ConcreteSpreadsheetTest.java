package info.kwarc.sissi.model.document.spreadsheet;

import info.kwarc.sally.networking.CometD;
import info.kwarc.sally.networking.interfaces.IConnectionManager;
import info.kwarc.sally.networking.interfaces.INetworkSenderAdapter;
import info.kwarc.sally.spreadsheet.WorksheetDocument;
import info.kwarc.sally.spreadsheet.interfaces.WorksheetFactory;

import org.apache.commons.codec.binary.Base64;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import sally.AlexData;
import sally.SpreadsheetModel;

import com.google.inject.AbstractModule;
import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.assistedinject.FactoryModuleBuilder;
import com.google.inject.name.Names;
import com.google.protobuf.AbstractMessage;
import com.google.protobuf.InvalidProtocolBufferException;


public class ConcreteSpreadsheetTest  {
	Injector i;
	CometD cometd;
	WorksheetFactory factory;
	Logger log;
	INetworkSenderAdapter sender;

	IConnectionManager manager = new IConnectionManager() {
		@Override
		public void newClient(String clientID) {
			log.info("client "+clientID+ " connected");
		}

		@Override
		public void newMessage(String clientID, String type, Object data) {
		}

		public void  test1(WorksheetDocument doc) {
			doc.getData("Vendor A", 7, 7, 1, 5);
		}
		
		@Override
		public void newMessage(String clientID, AbstractMessage msg) {
			if (msg instanceof AlexData) {
				AlexData alexData = (AlexData)msg;
				byte[] res = Base64.decodeBase64(alexData.getData());

				SpreadsheetModel rr = null;
				try {
					rr = SpreadsheetModel.parseFrom(res);
					WorksheetDocument doc = factory.create(alexData.getFileName(), rr, sender.create(clientID));
					test1(doc);
				} catch (InvalidProtocolBufferException e) {
					e.printStackTrace();
				}
			}
		}

		@Override
		public void disconnect(String clientID) {
		}

	};
	
	public ConcreteSpreadsheetTest() {
		log = LoggerFactory.getLogger(getClass());
		i = Guice.createInjector(new AbstractModule() {

			@Override
			protected void configure() {
				install(new FactoryModuleBuilder().build(WorksheetFactory.class));

				bind(CometD.class);
				bind(INetworkSenderAdapter.class).toProvider(CometD.class);
				bind(Integer.class).annotatedWith(Names.named("SallyPort")).toInstance(8181);
				bind(IConnectionManager.class).toInstance(manager);
			}
		});

		cometd = i.getInstance(CometD.class);
		factory = i.getInstance(WorksheetFactory.class);
		cometd.start();
		this.sender = i.getInstance(INetworkSenderAdapter.class);
	}

	public static void main(String[] args) {
		new ConcreteSpreadsheetTest();
	}

}
