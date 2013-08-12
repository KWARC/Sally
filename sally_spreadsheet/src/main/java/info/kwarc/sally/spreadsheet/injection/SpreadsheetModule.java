package info.kwarc.sally.spreadsheet.injection;

import info.kwarc.sally.spreadsheet.ASMEditor;
import info.kwarc.sally.spreadsheet.interfaces.WorksheetFactory;

import com.google.inject.AbstractModule;
import com.google.inject.assistedinject.FactoryModuleBuilder;

public class SpreadsheetModule extends AbstractModule{

	@Override
	protected void configure() {
		install(new FactoryModuleBuilder().build(WorksheetFactory.class));
		
		bind(ASMEditor.class);
	}

}
