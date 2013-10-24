package info.kwarc.sissi.model.document.spreadsheet;
/*
import info.kwarc.sally.model.document.spreadsheet.ASMInterface;

import java.io.BufferedOutputStream;
import java.io.ByteArrayOutputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Arrays;
import java.util.List;

import org.apache.commons.codec.binary.Base64;

import net.sf.ehcache.store.MemoryOnlyStore;
import sally.CellData;
import sally.CellPosition;
import sally.CellSpaceInformation;
import sally.DataParameter;
import sally.FBCreateData;
import sally.LegendCreateData;
import sally.RangeData;
import sally.SpreadsheetModel;
import sally.RangeData.Builder;

import com.hp.hpl.jena.rdf.model.Model;

public class FexData {
	ASMInterface asm;

	public FexData() {
		asm = new ASMInterface("http://fex-paper");
	}

	Integer createRowFB(int sheet, int startRow, int startCol, String [] content, Integer [] ids) {
		if (content.length == 0) {
			return null;
		}
		return createFB(sheet, startRow, startCol, startRow, startCol+content.length-1, new String[][] {content}, ids);
	}

	Integer createColFB(int sheet, int startRow, int startCol, String [] content, Integer [] ids) {
		if (content.length == 0) {
			return null;
		}
		String [][] c = new String[content.length][1];
		for (int i=0; i<content.length; ++i)
			c[i][0] = content[i];
		return createFB(sheet, startRow, startCol, startRow+content.length-1, startCol, c, ids);
	}

	Integer createFB(int sheet, int startRow, int startCol, int endRow, int endCol, String [][] content, Integer [] ids) {
		FBCreateData.Builder createData = FBCreateData.newBuilder();
		RangeData.Builder range = RangeData.newBuilder();
		for (int i=startRow; i<=endRow; ++i) {
			for (int j=startCol; j<=endCol; ++j) {
				CellData data = CellData.newBuilder().setPosition(sally.CellSpaceInformation.newBuilder().setWidth(1).setHeight(1).setPosition( sally.CellPosition.newBuilder().setSheet(sheet).setCol(j).setRow(i).build()).build()).setValue(content[i-startRow][j-startCol]).build();
				range.addCells(data);
			}
		}
		createData.setRange(range.build());
		List<Integer> list = Arrays.asList(ids);
		createData.addAllLegends(list);
		createData.setParameter(DataParameter.SameContentSameElement);
		return asm.createFB(createData.build());
	}

	// This should be used for header and titles of data
	Integer setHeaderLabel(int sheet, int startRow, int startCol, int length, String text) {
		String [] names = new String[length];
		for (int i=0; i<length; ++i)
			names[i] = text;
		return setRowTableHeaders(sheet, startRow, startCol, names);
	}

	Integer setRowTableHeaders(int sheet, int startRow, int startCol, String [] text) {
		Builder rangeData = RangeData.newBuilder();
		for (int i=0; i<text.length; ++i) {
			CellData data = CellData.newBuilder().setPosition(sally.CellSpaceInformation.newBuilder().setWidth(1).setHeight(1).setPosition( sally.CellPosition.newBuilder().setSheet(sheet).setCol(i+startCol).setRow(startRow).build()).build()).setValue(text[i]).build();
			rangeData.addCells(data);
		}
		
		return asm.createLegend(LegendCreateData.newBuilder().setFileName("IUI.xls").setItems(rangeData).setParameter(DataParameter.SameContentSameElement).build());
	}

	Integer setColTableHeaders(int sheet, int startRow, int startCol, String [] text) {
		Builder rangeData = RangeData.newBuilder();
		for (int i=0; i<text.length; ++i) {
			CellData data = CellData.newBuilder().setPosition(sally.CellSpaceInformation.newBuilder().setWidth(1).setHeight(1).setPosition( sally.CellPosition.newBuilder().setSheet(sheet).setCol(startCol).setRow(startRow+i).build()).build()).setValue(text[i]).build();
			rangeData.addCells(data);
		}
		return asm.createLegend(LegendCreateData.newBuilder().setFileName("IOI.xls").setItems(rangeData).setParameter(DataParameter.SameContentSameElement).build());
	}

	public String setData() {
		Integer wid = asm.getWorksheetIDByName("Vendor A");
		
		Integer vendA = setHeaderLabel(wid, 1, 1, 8, "Price List of Vendor A");
		//asm.addOntologyLink(vendA, "http://info.kwarc.sissi.winograd/vendor-A");
		asm.addOntologyLink(vendA, "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?price?seller");
		
		Integer discountMinQuantity = setRowTableHeaders(wid, 4, 1, new String[] {"100", "1000", "10000", ">10000"} );
		Integer discountRatesFB = createRowFB(wid, 5, 1, new String[] {"100.000%", "99.000%", "95.000%", "90.000%"}, new Integer [] {vendA, discountMinQuantity});
		//asm.addOntologyLink(discountMinQuantity, "http://info.kwarc.sissi.winograd/discount-min-quantities");
		asm.addOntologyLink(discountMinQuantity,  "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?price?minimum-purchase");
		//asm.addOntologyLink(discountRatesFB, "http://info.kwarc.sissi.winograd/discount-rates");
		asm.addOntologyLink(discountRatesFB,  "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?price?discount");
		
		Integer tableProps = setRowTableHeaders(wid, 7, 1, new String[] {"Component", "Thread", "Color", "Head", "Type", "Basic Price"});

		Integer componentCol = setColTableHeaders(wid, 8, 1, new String[] {"bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "bolt", "nut", "nut", "gasket", "flange", "flange", "flange", "blind flange", "blind flange", "blind flange" });
		Integer threadCol = setColTableHeaders(wid, 8, 2, new String[] { "M10", "M10", "M10", "M10", "M10", "M10", "M16", "M16", "M10", "M16", "_", "M10", "M10", "M16", "M10", "M16", "M17"});
		Integer colorCol = setColTableHeaders(wid, 8, 3, new String[] { "silver", "silver", "black", "silver", "red", "black", "black", "black", "black", "black", "_", "black", "silver", "black", "black", "black", "black"});
		Integer headCol = setColTableHeaders(wid, 8, 4, new String[] { "carriage", "stove", "machine", "machine", "machine", "machine", "machine", "machine", "_", "_", "_", "_", "_", "_", "_", "_", "_" });
		Integer typeCol = setColTableHeaders(wid, 8, 5, new String[] { "_", "_", "_", "_", "_", "_", "_", "_", "_", "_", "standard", "_", "_", "_", "_", "_", "_"});

		Integer cost = createColFB(wid, 8, 6, new String[] {"0.450 €", "0.460 €", "0.300 €", "0.310 €", "0.340 €", "0.350 €", "0.300 €", "0.350 €", "0.504 €", "0.498 €", "2.040 €", "1.080 €", "1.080 €", "1.090 €", "0.888 €", "0.888 €", "0.888 €"}, new Integer [] {componentCol, threadCol, colorCol, headCol, typeCol});

		//asm.addOntologyLink(componentCol, "http://info.kwarc.sissi.winograd/component-type");
		asm.addOntologyLink(componentCol, "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?solidobj?type");
		//asm.addOntologyLink(threadCol, "http://info.kwarc.sissi.winograd/thread-type");
		asm.addOntologyLink(threadCol, "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?thread?screw-thread");
		//asm.addOntologyLink(colorCol, "http://info.kwarc.sissi.winograd/color");
		asm.addOntologyLink(colorCol, "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?color?color ");
		//asm.addOntologyLink(headCol, "http://info.kwarc.sissi.winograd/head-type");
		asm.addOntologyLink(headCol, "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?nutbolt?head");
		//asm.addOntologyLink(typeCol, "http://info.kwarc.sissi.winograd/component-type");
		asm.addOntologyLink(typeCol, "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?solidobj?type");
		//asm.addOntologyLink(cost, "http://info.kwarc.sissi.winograd/cost");
		asm.addOntologyLink(cost, "http://tnt.kwarc.info/repos/stc/sissi/flange/cds/price.omdoc?price?price");
		
		return "winograd-model.rdf";
	}
	

	public void writeProto(String fileName) {
		OutputStream file;
		try {
			file = new FileOutputStream(fileName);
			ByteArrayOutputStream so = new ByteArrayOutputStream();
			SpreadsheetModel model = getAsm().serialize();
			model.writeTo(so);
			byte[] b = so.toByteArray();
			file.write(Base64.encodeBase64(b));
			file.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public String setDataFex() {
		String fileName = "formulaExplorer-asm.rdf";
		Integer wid = asm.getWorksheetIDByName("Summer1");
		
		Integer city = setHeaderLabel(wid, 1, 3, 1, "Bremen");
		asm.addOntologyLink(city, "http://tnt.kwarc.info/repos/stc/sissi/fex/cds/fex.omdoc?fex?Bremen");
		
		Integer fbColDays = setRowTableHeaders(wid, 2, 4, new String[] {"Day1", "Day2", "Day3", "Day4"});
		asm.addOntologyLink(fbColDays, "http://tnt.kwarc.info/repos/stc/sissi/fex/cds/fex.omdoc?fex?fexDay");
		
		Integer fbRowSunUnits = setColTableHeaders(wid, 3, 3,new String[] {"SunUnits"});
		Integer fbRowRainUnits = setColTableHeaders(wid, 5, 3,new String[] {"RainUnits"});
		asm.addOntologyLink(fbRowSunUnits, "http://tnt.kwarc.info/repos/stc/sissi/fex/cds/fex.omdoc?fex?fexUnit");
		asm.addOntologyLink(fbRowRainUnits, "http://tnt.kwarc.info/repos/stc/sissi/fex/cds/fex.omdoc?fex?fexUnit");
		createRowFB(wid, 3,4, new String[] {"1", "2", "1", "0"}, new Integer [] {fbRowSunUnits, fbColDays});
		createRowFB(wid, 5,4, new String[] {"8", "8", "8", "8"}, new Integer [] {fbRowRainUnits, fbColDays});
		
		Integer fbRowSunDeviation = setColTableHeaders(wid, 4, 3,new String[] {"MeanSunDeviation"});
		Integer fbRowRainDeviation = setColTableHeaders(wid, 6, 3,new String[] {"MeanRainDeviation"});
		asm.addOntologyLink(fbRowSunDeviation, "http://tnt.kwarc.info/repos/stc/sissi/fex/cds/fex.omdoc?fex?standard-deviation");
		asm.addOntologyLink(fbRowRainDeviation, "http://tnt.kwarc.info/repos/stc/sissi/fex/cds/fex.omdoc?fex?standard-deviation");
		createRowFB(wid, 4,4, new String[] {"0", "1", "0", "-1"}, new Integer [] {fbRowSunDeviation, fbColDays});
		createRowFB(wid, 6,4, new String[] {"0", "0", "0", "0"}, new Integer [] {fbRowRainDeviation, fbColDays});
		
		Integer fbColMean = setRowTableHeaders(wid, 2, 8, new String[] {"Mean"});
		asm.addOntologyLink(fbColMean, "http://tnt.kwarc.info/repos/stc/sissi/fex/cds/fex.omdoc?fex?mean");
		//Integer fbRowSunMean = setColTableHeaders(wid, 3, 8,new String[] {"SunMean"});
		//Integer fbRowRainMean = setColTableHeaders(wid, 5, 8,new String[] {"RainMean"});
		Integer fbRowSunMean=createRowFB(wid, 3,8, new String[] {"1"}, new Integer [] {fbColMean});
		Integer fbRowRainMean= createRowFB(wid, 5,8, new String[] {"8"}, new Integer [] {fbColMean});
		asm.addOntologyLink(fbRowSunMean, "http://tnt.kwarc.info/repos/stc/sissi/fex/cds/fex.omdoc?fex?meanSun");
		asm.addOntologyLink(fbRowRainMean, "http://tnt.kwarc.info/repos/stc/sissi/fex/cds/fex.omdoc?fex?meanRain");
		
		//Integer fbRowMeanOfMeans = setColTableHeaders(wid, 7, 8,new String[] {"MeanOfMeans"});
		Integer fbRowMeanOfMeans=createRowFB(wid, 7,8, new String[] {"4.5"}, new Integer [] {fbColMean});
		asm.addOntologyLink(fbRowMeanOfMeans, "http://tnt.kwarc.info/repos/stc/sissi/fex/cds/fex.omdoc?fex?meanMeans");
		
		Integer fbColVariance = setRowTableHeaders(wid, 2, 2, new String[] {"blankVariance"});
		Integer fbRowSunVariance = setColTableHeaders(wid, 4, 1,new String[] {"SunVariance"});
		Integer fbRowRainVariance = setColTableHeaders(wid, 6, 1,new String[] {"RainVariance"});
		asm.addOntologyLink(fbRowSunVariance, "http://tnt.kwarc.info/repos/stc/sissi/fex/cds/fex.omdoc?fex?sample-variance");
		asm.addOntologyLink(fbRowRainVariance, "http://tnt.kwarc.info/repos/stc/sissi/fex/cds/fex.omdoc?fex?sample-variance");
		//asm.getDependentCells(position)
		createRowFB(wid, 4,2, new String[] {"0.666667"}, new Integer [] {fbRowSunVariance, fbColVariance});
		createRowFB(wid, 6,2, new String[] {"0"}, new Integer [] {fbRowRainVariance, fbColVariance});
		
		return fileName;
		
	}

	public void index(String fileName) {
		OutputStream file;
		try {
			file = new FileOutputStream(fileName);
			asm.getRDFModel().write(file);
			Model model = asm.getRDFModel();
			file.close();
			writeProto(fileName+".b64");
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public ASMInterface getAsm() {
		return asm;
	}
	
	public Model getModel() {
		return asm.getRDFModel();
	}
	
	public static void main(String[] args) {
		FexData t = new FexData();
		t.index(t.setData());
	}
}*/